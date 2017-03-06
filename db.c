#include "db.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h>
#include <errno.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <string.h>

/**
 * Internal index file constant
 */
#define IDXLEN_SZ	4
#define SEP		':'
#define SPACE		' '
#define NEWLINE	'\n'

/**
 * hash chains
 */
#define PTR_SZ		7
#define PTR_MAX	999999
#define NHASH_DEF	137
#define FREE_OFF	0
#define HASH_OFF	PTR_SZ

typedef unsigned long DBHASH;
typedef unsigned long COUNT;

/**
 * Library's private representation of the database.
 */
typedef struct 
{
	int idxfd;	/* fd for index file*/
	int datfd;	/* fd for data file */
	char * idxbuf;
	char * datbuf;
	char * name;
	off_t idxoff;
	size_t idxlen;
	off_t datoff;
	size_t datlen;
	off_t ptrval;
	off_t ptroff;
	off_t chainoff;
	off_t hashoff;
	DBHASH nhash;
	COUNT cnt_delok;
	COUNT cnt_delerr;
	COUNT cnt_fetchok;
	COUNT cnt_fetcherr;
	COUNT cnt_nextrec;
	COUNT cnt_stor1;
	COUNT cnt_stor2;
	COUNT cnt_stor3;
	COUNT cnt_stor4;
	COUNT cnt_storerr;
} DB;

/**
 * Internal functions.
 */

static DB * 	_db_alloc(int);
static void	_db_dodelete(DB *);
static int 	_db_find_and_lock(DB *, const char *, int);
static int 	_db_findfree(DB *, int, int);
static void	_db_free(DB *);
static DBHASH 	_db_hash(DB *, const char *);
static char *	_db_readdat(DB *);
static off_t	_db_readidx(DB *, off_t);
static off_t	_db_readptr(DB *, off_t);
static void	_db_writedat(DB *, const char *, off_t, int);
static void	_db_writeidx(DB *, const char *, off_t, int, off_t);
static void	_db_writeptr(DB *, off_t, off_t);

/**
 * lock an area
 */
static int lock_reg(int fd, int cmd, int type, off_t offset, int whence, off_t len)
{
	struct flock lock;

	lock.l_type = type;		/*F_RDLCK, F_WRLCK, F_UNLCK*/
	lock.l_start = offset;		
	lock.l_whence = whence;
	lock.l_len = len;

	return fcntl(fd, cmd, &lock);
}

#define writew_lock(fd, offset, whence, len) \
	lock_reg((fd), F_SETLKW, F_WRLCK, (offset), (whence), (len))
#define readw_lock(fd, offset, whence, len) \
	lock_reg((fd), F_SETLKW, F_RDLCK, (offset), (whence), (len))
#define un_lock(fd, offset, whence, len) \
	lock_reg((fd), F_SETLK, F_UNLCK, (offset), (whence), (len))

/**
 * report error and exit
 */
static void err_exit(char *str)
{
	fprintf(stderr, "%s\n", str);
	exit(1);
}

/**
 * Open or create a database.
 */
DBHANDLE db_open(const char *pathname, int oflag, ...)
{
	DB 	*db;
	int 	len, mode;
	size_t 	i;
	char	asciiptr[PTR_SZ + 1],
		hash[(NHASH_DEF + 1) * PTR_SZ + 2];
	struct stat statbuff;

	/**
	 * allocate a DB structure, and the buffers it needs.
	 */
	len = strlen(pathname);
	if((db = _db_alloc(len)) == NULL){
		err_exit("db_open: _db_alloc error for DB");
	}
	db->nhash = NHASH_DEF;
	db->hashoff = HASH_OFF;
	strcpy(db->name, pathname);
	strcat(db->name, ".idx");

	if(oflag & O_CREAT){
		va_list ap;

		va_start(ap, oflag);
		mode = va_arg(ap, int);
		va_end(ap);

		/**
		 * open index file and data file.
		 */
		db->idxfd = open(db->name, oflag, mode);
		strcpy(db->name + len, ".dat");
		db->datfd = open(db->name, oflag, mode);
	} else {
		db->idxfd = open(db->name, oflag);
		strcpy(db->name + len, ".dat");
		db->datfd = open(db->name, oflag);
	}

	if(db->idxfd < 0 || db->datfd < 0){
		_db_free(db);
		return NULL;
	}

	if((oflag & (O_CREAT | O_TRUNC)) == (O_CREAT | O_TRUNC)){
		/**
		 * If the database was created, we have to initialize it.
		 * Write lock the entire file so that we can stat it.
		 */
		if(writew_lock(db->idxfd, 0, SEEK_SET, 0) < 0)
			err_exit("db_open: writew_lock error");

		if(fstat(db->idxfd, &statbuff) < 0)
			err_exit("db_open: fstat error");

		if(statbuff.st_size == 0){
			/**
			 * We have to build a list of (NHASH_DEF + 1) chain ptrs with a value of 0.
			 * The +1 is for the free list pointer that precedes the hash table.
			 */
			sprintf(asciiptr, "%*d", PTR_SZ, 0);
			hash[0] = 0;
			for(i = 0; i < NHASH_DEF; i++)
				strcat(hash, asciiptr);
			strcat(hash, "\n");
			i = strlen(hash);
			if(write(db->idxfd, hash, i) != i)
				err_exit("db_open: index file init write error");
		}

		if(un_lock(db->idxfd, 0, SEEK_SET, 0) < 0)
			err_exit("db_open: un_lock error");
	}
	db_rewind(db);
	return db;
}

/**
 * Allocate & initialize a DB structure and its buffers.
 */
static DB * _db_alloc(int namelen)
{
	DB *db;

	if((db = calloc(1, sizeof(DB))) == NULL)
		err_exit("_db_alloc: calloc error for DB");
	db->idxfd = db->datfd = -1;

	/**
	 * Allocate room for name. +5 for ".idx" or ".dat" plus null at end.
	 */
	if((db->name = malloc(namelen + 5)) == NULL)
		err_exit("_db_alloc: malloc error for name");

	/**
	 * Allcate an index buffer and a data buffer
	 * +2 for new line and null at end.
	 */
	if((db->idxbuf = malloc(IDXLEN_MAX + 2)) == NULL)
		err_exit("_db_alloc: malloc error for index buffer");
	if((db->datbuf = malloc(DATLEN_MAX + 2)) == NULL)
		err_exit("_db_alloc: malloc error for data buffer");

	return db;
}

/**
 * Relinquish  access to the database
 */
void db_close(DBHANDLE h)
{
	_db_free((DB *)h);	/*close fds, free buffers & struct*/
}

/**
 * Free up a DB structure, and all the malloc'ed buffers. Close all file descriptors
 */
static void _db_free(DB *db)
{
	if(db->idxfd >= 0)
		close(db->idxfd);
	if(db->datfd >= 0)
		close(db->datfd);
	if(db->idxbuf != NULL)
		free(db->idxbuf);
	if(db->datbuf != NULL)
		free(db->datbuf);
	if(db->name != NULL)
		free(db->name);
	free(db);
}

char * db_fetch(DBHANDLE h, const char * key)
{
	DB * db = h;
	char *ptr;

	if(_db_find_and_lock(db, key, 0) < 0){
		ptr = NULL;		/* error, record not found */
		db->cnt_fetcherr++;
	} else {
		ptr = _db_readdat(db);	/* return pointer to data */
		db->cnt_fetchok++;
	}

	/**
	 * Unlock the hash chain that _db_find_and_lock locked.
	 */
	if(un_lock(db->idxfd, db->chainoff, SEEK_SET, 1) < 0)
		err_exit("db_fetch: unlock error");

	return ptr;
}

/**
 * Find the specified record. Return with the hash chain locked.
 */
static int _db_find_and_lock(DB *db, const char *key, int writelock)
{
	off_t offset, nextoffset;

	/**
	 * Calculate the hash value for this key, then calculate the byte offset of corresponding 
	 * chain ptr in hash table.
	 */
	db->chainoff = (_db_hash(db, key) * PTR_SZ) + db->hashoff;
	db->ptroff = db->chainoff;

	/**
	 * We lock the chain here. The caller must unlock it when done.
	 * Note we lock and unlock only the first byte.
	 */
	if(writelock){
		if(writew_lock(db->idxfd, db->chainoff, SEEK_SET, 1) < 0)
			err_exit("_db_find_and_lock: writew_lock error");
	} else {
		if(readw_lock(db->idxfd, db->chainoff, SEEK_SET, 1) < 0)
			err_exit("_db_find_and_lock: readw_lock error");
	}

	/**
	 * Get the offset in the index file of first record on hash chain (can be 0).
	 */
	offset = _db_readptr(db, db->ptroff);
	while(offset != 0){
		nextoffset = _db_readidx(db, offset);
		if(strcmp(db->idxbuf, key) == 0)
			break;
		db->ptroff = offset;
		offset = nextoffset;
	}
	/**
	 * offset == 0 on error (record not found)
	 */
	return (offset == 0 ? -1 : 0); 
}

/**
 * Calculate the hash value for a key
 */
static DBHASH _db_hash(DB * db, const char * key)
{
	DBHASH hval = 0;
	char c;
	int i;

	for(i = 1; (c = *key++) != 0; i++)
		hval += c * i;
	return (hval % db->nhash);
}

/**
 * Read a chain ptr field from anywhere in the index file
 */
static off_t _db_readptr(DB *db, off_t offset)
{
	char asciiptr[PTR_SZ + 1];
	if(lseek(db->idxfd, offset, SEEK_SET) == -1)
		err_exit("_db_readptr: lseek error to ptr field");
	if(read(db->idxfd, asciiptr, PTR_SZ) != PTR_SZ)
		err_exit("_db_readptr: read error of ptr field");
	asciiptr[PTR_SZ] = 0;
	return atol(asciiptr);
}

/**
 * Read the current index record.
 * Return next index offset
 */
static off_t _db_readidx(DB *db, off_t offset)
{
	ssize_t i;
	char *ptr1, *ptr2;
	char asciiptr[PTR_SZ + 1], asciilen[IDXLEN_SZ + 1];
	struct iovec iov[2];

	if((db->idxoff = lseek(db->idxfd, offset, offset == 0 ? SEEK_CUR : SEEK_SET)) == -1)
		err_exit("_db_readidx: lseek error");

	iov[0].iov_base = asciiptr;
	iov[0].iov_len = PTR_SZ;
	iov[1].iov_base = asciilen;
	iov[1].iov_len = IDXLEN_SZ;

	if((i = readv(db->idxfd, &iov[0], 2)) != PTR_SZ + IDXLEN_SZ){
		if(i == 0 && offset == 0)
			return -1;	/* EOF for db_nextrec */
		err_exit("_db_readidx: readv error of index record");
	}

	asciiptr[PTR_SZ] = 0;
	db->ptrval = atol(asciiptr);

	asciilen[IDXLEN_SZ] = 0;
	if((db->idxlen = atoi(asciilen)) < IDXLEN_MIN || db->idxlen > IDXLEN_MAX)
		err_exit("_db_readidx: invalid length");

	/**
	 * Now read the actual index record.
	 */
	if((i = read(db->idxfd, db->idxbuf, db->idxlen)) != db->idxlen)
		err_exit("_db_readidx: read error of index record");

	if(db->idxbuf[db->idxlen - 1] != NEWLINE)
		err_exit("_db_readidx: missing newline");

	db->idxbuf[db->idxlen - 1] = 0;	/* replace newline with null */

	/**
	 * Find the separators in the index record
	 */
	if((ptr1 = strchr(db->idxbuf, SEP)) == NULL)
		err_exit("_db_readidx: missing first separator");
	*ptr1++ = 0;

	if((ptr2 = strchr(db->idxbuf, SEP)) == NULL)
		err_exit("_db_readidx: missing second separator");
	*ptr2++ = 0;

	if(strchr(ptr2, SEP) != NULL)
		err_exit("_db_readidx: too many separators");

	/**
	 * Get the starting offset and length of data record.
	 */
	if((db->datoff = atol(ptr1)) < 0)
		err_exit("_db_readidx: starting offset < 0");
	if((db->datlen = atol(ptr2)) <= 0 || db->datlen > DATLEN_MAX)
		err_exit("_db_readidx: invalid length");
	return db->ptrval;	/* return offset of next key in chain */
}

/**
 * Read the current data record into data buffer.
 */
static char * _db_readdat(DB *db)
{
	if(lseek(db->datbuf, db->datoff, SEEK_SET) == -1)
		err_exit("_db_readdat: lseek error");
	if(read(db->datfd, db->datbuf, db->datlen) != db->datlen)
		err_exit("_db_readdat: read error");
	if(db->datbuf[db->datlen - 1] != NEWLINE)
		err_exit("_db_readdat: missing newline");
	db->datbuf[db->datlen - 1] = 0;
	return db->datbuf;
}

/**
 * Delete the specified record
 */
int db_delete(DBHANDLE h, const char * key)
{
	DB *db = h;
	int rc = 0;

	if(_db_find_and_lock(db, key, 1) == 0){
		_db_dodelete(db);
		db->cnt_delok++;
	} else {
		rc = -1;			/* not found */
		db->cnt_delerr++;
	}
	if(un_lock(db->idxfd, db->chainoff, SEEK_SET, 1) < 0)
		err_exit("db_delete: un_lock error");
	return rc;
}

/**
 * Delete the current record sepecified by the DB structure.
 */
static void _db_dodelete(DB *db)
{
	int i;
	char *ptr;
	off_t freeptr, saveptr;

	/**
	 * Set data buffer and key to all blanks.
	 */
	for(ptr = db->datbuf, i = 0; i < db->datlen - 1; i++)
		*ptr++ = SPACE;
	*ptr = 0;
	ptr = db->idxbuf;
	while(*ptr)
		*ptr++ = SPACE;

	/**
	 * Lock the free list.
	 */
	if(writew_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("_db_dodelete: writew_lock error");

	/**
	 * Write the data record with all blanks.
	 */
	_db_writedat(db, db->datbuf, db->datoff, SEEK_SET);

	/**
	 * Read the free list pointer. 
	 * Its value becoms the chain ptr field of the deleted index record.
	 */
	freeptr = _db_readptr(db, FREE_OFF);

	/**
	 * Save the contents of index record chain ptr.
	 */
	saveptr = db->ptrval;

	/**
	 * Rewrite the index record.
	 */
	_db_writeidx(db, db->idxbuf, db->idxoff, SEEK_SET, freeptr);

	/**
	 * Write the new free list pointer
	 */
	_db_writeptr(db, FREE_OFF, db->idxoff);

	/**
	 * Rewrite the chain ptr. 
	 */
	_db_writeptr(db, db->ptroff, saveptr);
	if(un_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("_db_dodelete: un_lock error");
}

/**
 * Write a data record.
 */
static void _db_writedat(DB *db, const char *data, off_t offset, int whence)
{
	struct iovec iov[2];
	static char newline = NEWLINE;

	/**
	 * If we're appending, we have to lock before doing the lseek and write 
	 * to make the two an atomic operation
	 */
	if(whence == SEEK_END)
		if(writew_lock(db->datfd, 0, SEEK_SET, 0) < 0)
			err_exit("_db_writedat: writew_lock error");

	if((db->datoff = lseek(db->datfd, offset, whence)) == -1)
		err_exit("_db_writedat: lseek error");
	db->datlen = strlen(data) + 1; 		/* datalen includes newline */

	iov[0].iov_base = (char *)data;
	iov[0].iov_len = db->datlen - 1;
	iov[1].iov_base = &newline;
	iov[1].iov_len = 1;
	if(writev(db->datfd, &iov[0], 2) != db->datlen)
		err_exit("_db_writedat: writev error of data record");

	if(whence == SEEK_END)
		if(un_lock(db->datfd, 0, SEEK_SET, 0) < 0)
			err_exit("_db_writedat: un_lock error");
}

/**
 * Write an index record.
 */
static void _db_writeidx(DB *db, const char *key, off_t offset, int whence, off_t ptrval)
{
	struct iovec iov[2];
	char asciiptrlen[PTR_SZ + IDXLEN_SZ + 1];
	int len;

	if((db->ptrval = ptrval) < 0 || ptrval > PTR_MAX)
		err_exit("_db_writeidx: invalid ptr: %d", ptrval);
	sprintf(db->idxbuf, "%s%c%lld%c%ld\n", key, SEP, (long long)db->datoff, SEP, (long)db->datlen);
	len = strlen(db->idxbuf);
	if(len < IDXLEN_MIN || len > IDXLEN_MAX)
		err_exit("_db_writeidx: invalid length");
	sprintf(asciiptrlen, "%*lld%*d", PTR_SZ, (long long)ptrval, IDXLEN_SZ, len);

	/**
	 * If we are appending, we have to lock before doing the lseek and write 
	 * to make the two an atomic operation.
	 */
	if(whence == SEEK_END)
		if(writew_lock(db->idxfd, ((db->nhash + 1) * PTR_SZ) + 1, SEEK_SET, 0))
			err_exit("_db_writeidx: writew_lock error");

	/**
	 * Position the index file and record the offset.
	 */
	if((db->idxoff = lseek(db->idxfd, offset, whence)) == -1)
		err_exit("_db_writeidx: lseek error");

	iov[0].iov_base = asciiptrlen;
	iov[0].iov_len = PTR_SZ + IDXLEN_SZ;
	iov[1].iov_base = db->idxbuf;
	iov[1].iov_len = len;
	if(writev(db->idxfd, &iov[0], 2) != PTR_SZ + IDXLEN_SZ + len)
		err_exit("_db_writeidx: writev error of index record");

	if(whence == SEEK_END)
		if(un_lock(db->idxfd, ((db->nhash + 1)*PTR_SZ) + 1, SEEK_SET, 0) < 0)
			err_exit("_db_writeidx: un_lock error");
}

/**
 * Write a chain ptr field somewhere in the index file
 */
static void _db_writeptr(DB *db, off_t offset, off_t ptrval)
{
	char asciiptr[PTR_SZ + 1];

	if(ptrval < 0 || ptrval > PTR_MAX)
		err_exit("_db_writeptr: invalid ptr: %d", ptrval);
	sprintf(asciiptr, "%*lld", PTR_SZ, (long long)ptrval);

	if(lseek(db->idxfd, offset, SEEK_SET) == -1)
		err_exit("_db_writeptr: lseek error to ptr field");
	if(write(db->idxfd, asciiptr, PTR_SZ) != PTR_SZ)
		err_exit("_db_writeptr: write error of ptr field");
}

/**
 * Store a record in the database. Return 0 if OK, 1 if record exists and DB_INSERT specified,
 * -1 on error.
 */
int db_store(DBHANDLE h, const char *key, const char *data, int flag)
{
	DB *db = h;
	int rc, keylen, datlen;
	off_t ptrval;

	if(flag != DB_INSERT && flag != DB_REPLACE && flag != DB_STORE){
		errno = EINVAL;
		return -1;
	}
	keylen = strlen(key);
	datlen = strlen(data) + 1;		/* +1 for newline at end*/
	if(datlen < DATLEN_MIN || datlen > DATLEN_MAX)
		err_exit("db_store: invalid data length");

	/**
	 * _db_find_and_lock calculates which hash table this record goes into,
	 * regardless of whether it already exists or not.
	 */
	if(_db_find_and_lock(db, key, 1) < 0){		/* record not found */
		if(flag == DB_REPLACE){
			rc = -1;
			db->cnt_storerr++;
			errno = ENOENT;		/* error, record dose not exist */
			goto doreturn;
		}

		/**
		 * read the chain ptr to the first index record on hash chain.
		 */
		ptrval = _db_readptr(db, db->chainoff);
		
		if(_db_findfree(db, keylen, datlen) < 0){
			/**
			 * can't find an empty record big enough. Append the new
			 * record to the endsof the index and data files.
			 */
			_db_writedat(db, data, 0, SEEK_END);
			_db_writeidx(db, key, 0, SEEK_END, ptrval);

			/**
			 * db->idxoff was set by _db_writeidx.
			 */
			_db_writeptr(db, db->chainoff, db->idxoff);
			db->cnt_stor1++;
		} else {
			/**
			 * Reuse an empty record.
			 */
			_db_writedat(db, data, db->datoff, SEEK_SET);
			_db_writeidx(db, key, db->idxoff, SEEK_SET, ptrval);
			_db_writeptr(db, db->chainoff, db->idxoff);
			db->cnt_stor2++;
		}
	} else {		/* record found */
		if(flag == DB_INSERT){
			rc = 1;		/* error, record already in db */
			db->cnt_storerr++;
			goto doreturn;
		}

		/**
		 * We are replacing an existing record.
		 * We need to check if the data records are the same size.
		 */
		if(datlen != db->datlen){
			_db_dodelete(db);	/* delete the existing record */

			/**
			 * Reread the chain ptr in the hash table
			 */
			ptrval = _db_readptr(db, db->chainoff);

			/**
			 * Append new index and data records to end of files.
			 */
			_db_writedat(db, data, 0, SEEK_END);
			_db_writeidx(db, key, 0, SEEK_END, ptrval);

			/**
			 * New record goes to the front of the hash chain
			 */
			_db_writeptr(db, db->chainoff, db->idxoff);
			db->cnt_stor3++;
		} else {
			/**
			 * Same size data, just replace data record.
			 */
			_db_writedat(db, data, db->datoff, SEEK_SET);
			db->cnt_stor4++;
		}
	}
	rc = 0;		/* OK */
doreturn:
	if(un_lock(db->idxfd, db->chainoff, SEEK_SET, 1) < 0)
		err_exit("db_store: un_lock error");
	return rc;
}

/**
 * Try to find a free index record and accompanying data record of the correct sizes.
 */
static int _db_findfree(DB *db, int keylen, int datlen)
{
	int rc;
	off_t offset, nextoffset, saveoffset;

	/**
	 * Lock the free list
	 */
	if(writew_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("_db_findfree: writew_lock error");

	/**
	 * Read the free list pointer.
	 */
	saveoffset = FREE_OFF;
	offset = _db_readptr(db, saveoffset);
	while(offset != 0){
		nextoffset = _db_readidx(db, offset);
		if(strlen(db->idxbuf) == keylen && db->datlen == datlen)
			break;
		saveoffset = offset;
		offset = nextoffset;
	}

	if(offset == 0){
		rc = -1;		/*no match found*/
	} else {
		/**
		 * Found a free record with matching sizes.
		 */
		_db_writeptr(db, saveoffset, db->ptrval);
		rc = 0;
	}

	if(un_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("_db_findfree: un_lock error");
	return rc;
}

/**
 * Rewind the index file for db_nextrec
 */
void db_rewind(DBHANDLE h)
{
	DB *db = h;
	off_t offset;

	offset = (db->nhash + 1) * PTR_SZ;		/* +1 for free list ptr */

	if((db->idxoff = lseek(db->idxfd, offset + 1, SEEK_SET)) == -1)
		err_exit("db_rewind: lseek error");
}

/**
 * Return the next sequential record.
 */
char * db_nextrec(DBHANDLE h, char *key)
{
	DB *db = h;
	char c;
	char *ptr;

	/**
	 * We read lock the free list so that we don't read a record
	 * in the middle of its being deleted. 
	 */
	if(readw_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("db_nextrec: readw_lock error");
	do{
		/**
		 * Read next sequential index record
		 */
		if(_db_readidx(db, 0) < 0){
			ptr = NULL;		/* end of index file, EOF */
			goto doreturn;
		}

		/**
		 * Check if key is all blank (empty record).
		 */
		ptr = db->idxbuf	;
		while((c = *ptr++) != 0 && c == SPACE)
			;	/* skip until null byte or nonblank */
	} while(c == 0);		/* loop until a nonblank key is found */

	if(key !=NULL)
		strcpy(key, db->idxbuf);		/* return key */
	ptr = _db_readdat(db);		/* return pointer to data buffer */
	db->cnt_nextrec++;

doreturn:
	if(un_lock(db->idxfd, FREE_OFF, SEEK_SET, 1) < 0)
		err_exit("db_nextrec: un_lock error");
	return ptr;
}
