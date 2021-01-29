#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdalign.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <unistd.h>

#include "ext2fs_defs.h"
#include "ext2fs.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#undef DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* Call this function when an unfixable error has happened. */
static noreturn void panic(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  fputc('\n', stderr);
  va_end(ap);
  exit(EXIT_FAILURE);
}

/* Number of lists containing buffered blocks. */
#define NBUCKETS 16

/* Since majority of files in a filesystem are small, `idx` values will be
 * usually low. Since ext2fs tends to allocate blocks at the beginning of each
 * block group, `ino` values are less predictable. */
#define BUCKET(ino, idx) (((ino) + (idx)) % NBUCKETS)

/* That should give us around 64kB worth of buffers. */
#define NBLOCKS (NBUCKETS * 4)

/* Structure that is used to manage buffer of single block. */
typedef struct blk {
  TAILQ_ENTRY(blk) b_hash;
  TAILQ_ENTRY(blk) b_link;
  uint32_t b_blkaddr; /* block address on the block device */
  uint32_t b_inode;   /* i-node number of file this buffer refers to */
  uint32_t b_index;   /* block index from the beginning of file */
  uint32_t b_refcnt;  /* if zero then block can be reused */
  void *b_data;       /* raw data from this buffer */
} blk_t;

typedef TAILQ_HEAD(blk_list, blk) blk_list_t;

/* BLK_ZERO is a special value that reflect the fact that block 0 may be used to
 * represent a block filled with zeros. You must not dereference the value! */
#define BLK_ZERO ((blk_t *)-1L)

/* All memory for buffers and buffer management is allocated statically.
 * Using malloc for these would introduce unnecessary complexity. */
static alignas(BLKSIZE) char blkdata[NBLOCKS][BLKSIZE];
static blk_t blocks[NBLOCKS];
static blk_list_t buckets[NBUCKETS]; /* all blocks with valid data */
static blk_list_t lrulst;            /* free blocks with valid data */
static blk_list_t freelst;           /* free blocks that are empty */

/* File descriptor that refers to ext2 filesystem image. */
static int fd_ext2 = -1;

/* How many i-nodes fit into one block? */
#define BLK_INODES (BLKSIZE / sizeof(ext2_inode_t))

/* How many block pointers fit into one block? */
#define BLK_POINTERS (BLKSIZE / sizeof(uint32_t))

/* Properties extracted from a superblock and block group descriptors. */
static size_t inodes_per_group;      /* number of i-nodes in block group */
static size_t blocks_per_group;      /* number of blocks in block group */
static size_t group_desc_count;      /* numbre of block group descriptors */
static size_t block_count;           /* number of blocks in the filesystem */
static size_t inode_count;           /* number of i-nodes in the filesystem */
static size_t first_data_block;      /* first block managed by block bitmap */
static ext2_groupdesc_t *group_desc; /* block group descriptors in memory */

/*
 * Buffering routines.
 */

/* Opens filesystem image file and initializes block buffers. */
static int blk_init(const char *fspath) {
  if ((fd_ext2 = open(fspath, O_RDONLY)) < 0)
    return errno;

  /* Initialize list structures. */
  TAILQ_INIT(&lrulst);
  TAILQ_INIT(&freelst);
  for (int i = 0; i < NBUCKETS; i++)
    TAILQ_INIT(&buckets[i]);

  /* Initialize all blocks and put them on free list. */
  for (int i = 0; i < NBLOCKS; i++) {
    blocks[i].b_data = blkdata[i];
    TAILQ_INSERT_TAIL(&freelst, &blocks[i], b_link);
  }

  return 0;
}

/* Allocates new block buffer. */
static blk_t *blk_alloc(void) {
  blk_t *blk = NULL;

  /* Initially every empty block is on free list. */
  if (!TAILQ_EMPTY(&freelst)) {
    /* TODO */
    blk = TAILQ_FIRST(&freelst);
    TAILQ_REMOVE(&freelst, blk, b_link);
    return blk;
  }

  /* Eventually free list will become exhausted.
   * Then we'll take the last recently used entry from LRU list. */
  if (!TAILQ_EMPTY(&lrulst)) {
    /* TODO */
    blk = TAILQ_LAST(&lrulst, blk_list);
    int bucket_idx = BUCKET(blk->b_inode, blk->b_index);
    blk_list_t *bucket = &buckets[bucket_idx];
    TAILQ_REMOVE(&lrulst, blk, b_link);
    TAILQ_REMOVE(bucket, blk, b_hash);
    return blk;
  }

  /* No buffers!? Have you forgot to release some? */
  panic("Free buffers pool exhausted!");
}

/* Acquires a block buffer for file identified by `ino` i-node and block index
 * `idx`. When `ino` is zero the buffer refers to filesystem metadata (i.e.
 * superblock, block group descriptors, block & i-node bitmap, etc.) and `off`
 * offset is given from the start of block device. */
static blk_t *blk_get(uint32_t ino, uint32_t idx) {
  blk_list_t *bucket = &buckets[BUCKET(ino, idx)];
  blk_t *blk = NULL;

  /* Locate a block in the buffer and return it if found. */

  /* TODO */
  blk = TAILQ_FIRST(bucket);
  while (blk) {
    if (blk->b_inode == ino) {
      if (blk->b_refcnt < 1) {
        TAILQ_REMOVE(&lrulst, blk, b_link);
      }
      blk->b_refcnt++;
      return blk;
    }
    blk = TAILQ_NEXT(blk, b_hash);
  }

  long blkaddr = ext2_blkaddr_read(ino, idx);
  debug("ext2_blkaddr_read(%d, %d) -> %ld\n", ino, idx, blkaddr);
  if (blkaddr == -1)
    return NULL;
  if (blkaddr == 0)
    return BLK_ZERO;
  if (ino > 0 && !ext2_block_used(blkaddr))
    panic("Attempt to read block %d that is not in use!", blkaddr);

  blk = blk_alloc();
  blk->b_inode = ino;
  blk->b_index = idx;
  blk->b_blkaddr = blkaddr;
  blk->b_refcnt = 1;

  ssize_t nread =
    pread(fd_ext2, blk->b_data, BLKSIZE, blk->b_blkaddr * BLKSIZE);
  if (nread != BLKSIZE)
    panic("Attempt to read past the end of filesystem!");

  TAILQ_INSERT_HEAD(bucket, blk, b_hash);
  return blk;
}

/* Releases a block buffer. If reference counter hits 0 the buffer can be
 * reused to cache another block. The buffer is put at the beginning of LRU list
 * of unused blocks. */
static void blk_put(blk_t *blk) {
  if (--blk->b_refcnt > 0)
    return;

  TAILQ_INSERT_HEAD(&lrulst, blk, b_link);
}

/*
 * Ext2 filesystem routines.
 */

/* Reads block bitmap entry for `blkaddr`. Returns 0 if the block is free,
 * 1 if it's in use, and EINVAL if `blkaddr` is out of range. */
int ext2_block_used(uint32_t blkaddr) {
  if (blkaddr >= block_count)
    return EINVAL;
  int used = 0;
  /* TODO */
  if (!blkaddr) {
    return EINVAL;
  }

  uint32_t block_group_id = (blkaddr - 1) / blocks_per_group;
  blk_t *block_bitmap = blk_get(0, group_desc[block_group_id].gd_b_bitmap);
  uint32_t local_block_id = (blkaddr - 1) % blocks_per_group;

  /* 32 means four bytes. This came straight from stack overflow. */
  used = *((int *)(block_bitmap->b_data) + (local_block_id / 32)) &
         (1 << local_block_id % 32);

  blk_put(block_bitmap);

  return used;
}

/* Reads i-node bitmap entry for `ino`. Returns 0 if the i-node is free,
 * 1 if it's in use, and EINVAL if `ino` value is out of range. */
int ext2_inode_used(uint32_t ino) {
  if (!ino || ino >= inode_count)
    return EINVAL;
  int used = 0;
  /* TODO */
  uint32_t block_group_id = (ino - 1) / inodes_per_group;
  blk_t *inodes_bitmap = blk_get(0, group_desc[block_group_id].gd_i_bitmap);
  uint32_t local_inode_id = (ino - 1) % inodes_per_group;

  /* 32 means four bytes. This came straight from stack overflow. */
  used = *((int *)(inodes_bitmap->b_data) + (local_inode_id / 32)) &
         (1 << local_inode_id % 32);

  blk_put(inodes_bitmap);

  return used;
}

/* Reads i-node identified by number `ino`.
 * Returns 0 on success. If i-node is not allocated returns ENOENT. */
static int ext2_inode_read(off_t ino, ext2_inode_t *inode) {
  /* TODO */
  if (ext2_inode_used(ino)) {
    uint32_t block_group_id = (ino - 1) / inodes_per_group;
    uint32_t local_inode_id = (ino - 1) % inodes_per_group;
    size_t pos = (BLKSIZE * group_desc[block_group_id].gd_i_tables) +
                 (local_inode_id * sizeof(ext2_inode_t));
    ext2_read(0, inode, pos, sizeof(ext2_inode_t));
    return 0;
  }

  return ENOENT;
}

/* Returns block pointer `blkidx` from block of `blkaddr` address. */
static uint32_t ext2_blkptr_read(uint32_t blkaddr, uint32_t blkidx) {
  /* TODO */
  blk_t *blk = blk_get(0, blkaddr);
  uint32_t block_ptr = ((uint32_t *)blk->b_data)[blkidx];
  blk_put(blk);
  return block_ptr;
}

/* Translates i-node number `ino` and block index `idx` to block address.
 * Returns -1 on failure, otherwise block address. */
long ext2_blkaddr_read(uint32_t ino, uint32_t blkidx) {
  /* No translation for filesystem metadata blocks. */
  if (ino == 0)
    return blkidx;

  ext2_inode_t inode;
  if (ext2_inode_read(ino, &inode))
    return -1;

  /* Read direct pointers or pointers from indirect blocks. */

  /* TODO */
  /* Let's define some constants to make code clearer. */
  const int STEP_ONE = EXT2_NDADDR + BLK_POINTERS;
  const int STEP_TWO = STEP_ONE + (BLK_POINTERS * BLK_POINTERS);
  const int STEP_THREE =
    STEP_TWO + (BLK_POINTERS * BLK_POINTERS * BLK_POINTERS);

  /* Data can be found after one or two or three steps. */
  if (blkidx < EXT2_NDADDR) {
    return inode.i_blocks[blkidx];
  } else if (blkidx < STEP_ONE) {
    uint32_t indirect_block_id = blkidx - EXT2_NDADDR;
    uint32_t indirect_block_address = inode.i_blocks[EXT2_NDADDR];

    return ext2_blkptr_read(indirect_block_address, indirect_block_id);
  } else if (blkidx < STEP_TWO) {
    blkidx -= STEP_ONE;

    uint32_t indirect_block_pointer = blkidx / BLK_POINTERS;
    uint32_t indirect_block_address = inode.i_blocks[EXT2_NDADDR + 1];

    uint32_t second_indirect_block_pointer = blkidx % BLK_POINTERS;
    uint32_t second_indirect_block_address =
      ext2_blkptr_read(indirect_block_address, indirect_block_pointer);

    return ext2_blkptr_read(second_indirect_block_address,
                            second_indirect_block_pointer);
  } else if (blkidx < STEP_THREE) {
    blkidx -= STEP_TWO;

    uint32_t indirect_block_pointer = blkidx / (BLK_POINTERS * BLK_POINTERS);
    uint32_t indirect_block_address = inode.i_blocks[EXT2_NDADDR + 2];

    uint32_t second_indirect_block_pointer = blkidx / BLK_POINTERS;
    uint32_t second_indirect_block_address =
      ext2_blkptr_read(indirect_block_address, indirect_block_pointer);

    uint32_t third_indirect_block_pointer = blkidx % BLK_POINTERS;
    uint32_t third_indirect_block_address = ext2_blkptr_read(
      second_indirect_block_address, second_indirect_block_pointer);

    return ext2_blkptr_read(third_indirect_block_address,
                            third_indirect_block_pointer);
  }

  return -1;
}

/* Reads exactly `len` bytes starting from `pos` position from any file (i.e.
 * regular, directory, etc.) identified by `ino` i-node. Returns 0 on success,
 * EINVAL if `pos` and `len` would have pointed past the last block of file.
 *
 * WARNING: This function assumes that `ino` i-node pointer is valid! */
int ext2_read(uint32_t ino, void *data, size_t pos, size_t len) {
  /* TODO */
  uint32_t block_id = pos / BLKSIZE;
  uint32_t first_block_offset_from_start = pos % BLKSIZE;
  uint32_t first_block_offset_from_end =
    BLKSIZE - first_block_offset_from_start;
  uint32_t last_block_req_size = (pos + len) % BLKSIZE;
  uint32_t entire_blocks_to_read = len / BLKSIZE;

  if (first_block_offset_from_end + last_block_req_size == BLKSIZE) {
    entire_blocks_to_read--;
  }

  if (ino != 0) {
    ext2_inode_t inode;
    ext2_inode_read(ino, &inode);
    if (inode.i_size < pos + len)
      return EINVAL;
  }

  /* Special cases. */
  blk_t *blk = blk_get(ino, block_id);
  uint32_t first_entire_blk_pos = pos + first_block_offset_from_end;
  if (blk == BLK_ZERO) {
    memset(data, 0, len);
    return EXIT_SUCCESS;
  }
  if (pos + len <= first_entire_blk_pos) {
    memcpy(data, blk->b_data + first_block_offset_from_start, len);
    blk_put(blk);
    return EXIT_SUCCESS;
  }

  if (first_block_offset_from_end) {
    /* Read the first block. */
    memcpy(data, blk->b_data + first_block_offset_from_start,
           first_block_offset_from_end);
    blk_put(blk);
  }
  /* Read blocks from 2 to blocks_to_read. */
  for (uint32_t i = 0; i < entire_blocks_to_read; i++) {
    blk = blk_get(ino, block_id + i);
    memcpy(data + i * BLKSIZE + first_block_offset_from_end, blk->b_data,
           BLKSIZE);
    blk_put(blk);
  }
  if (last_block_req_size) {
    /* Read the last block. */
    blk = blk_get(ino, block_id + entire_blocks_to_read);
    void *last_data_block_ptr =
      data + entire_blocks_to_read * BLKSIZE + first_block_offset_from_end;
    memcpy(last_data_block_ptr, blk->b_data, last_block_req_size);
    blk_put(blk);
  }

  return EXIT_SUCCESS;
}

/* Reads a directory entry at position stored in `off_p` from `ino` i-node that
 * is assumed to be a directory file. The entry is stored in `de` and
 * `de->de_name` must be NUL-terminated. Assumes that entry offset is 0 or was
 * set by previous call to `ext2_readdir`. Returns 1 on success, 0 if there are
 * no more entries to read. */
#define de_name_offset offsetof(ext2_dirent_t, de_name)

int ext2_readdir(uint32_t ino, uint32_t *off_p, ext2_dirent_t *de) {
  /* TODO */
  ext2_inode_t inode;
  ext2_inode_read(ino, &inode);

  while (true) {
    if (inode.i_size <= *off_p) {
      return 0;
    }

    /* Read one byte. */
    ext2_read(ino, de, *off_p, 8);
    /* Read dir name. */
    ext2_read(ino, de->de_name, *off_p + 8, de->de_namelen);
    /* `de->de_name` must be NUL-terminated. */
    de->de_name[de->de_namelen] = '\0';
    *off_p += de->de_reclen;

    if (de->de_ino) {
      break;
    }
  }

  return 1;
}

/* Read the target of a symbolic link identified by `ino` i-node into buffer
 * `buf` of size `buflen`. Returns 0 on success, EINVAL if the file is not a
 * symlink or read failed. */
int ext2_readlink(uint32_t ino, char *buf, size_t buflen) {
  int error;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

  /* Check if it's a symlink and read it. */
  /* TODO */
  if ((EXT2_IFLNK != (inode.i_mode & EXT2_IFMT)) &&
      (ext2_read(ino, buf, 0, buflen) != EXIT_SUCCESS)) {
    return EINVAL;
  }

  if (inode.i_size < 60) {
    memcpy(buf, inode.i_blocks, inode.i_size);
    return 0;
  }

  return 0;
}

/* Read metadata from file identified by `ino` i-node and convert it to
 * `struct stat`. Returns 0 on success, or error if i-node could not be read. */
int ext2_stat(uint32_t ino, struct stat *st) {
  int error;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

  /* Convert the metadata! */

  /* TODO */
  st->st_blksize = (long)BLKSIZE;
  st->st_blocks = (blkcnt_t)inode.i_nblock;
  st->st_ino = (ino_t)ino;
  st->st_nlink = (nlink_t)inode.i_nlink;
  st->st_mode = (mode_t)inode.i_mode;
  st->st_atime = (time_t)inode.i_atime;
  st->st_mtime = (time_t)inode.i_mtime;
  st->st_ctime = (time_t)inode.i_ctime;
  st->st_size = (off_t)inode.i_size;
  st->st_uid = (uid_t)inode.i_uid;
  st->st_gid = (gid_t)inode.i_gid;

  return 0;
}

/* Reads file identified by `ino` i-node as directory and performs a lookup of
 * `name` entry. If an entry is found, its i-inode number is stored in `ino_p`
 * and its type in stored in `type_p`. On success returns 0, or EINVAL if `name`
 * is NULL or zero length, or ENOTDIR is `ino` file is not a directory, or
 * ENOENT if no entry was found. */
int ext2_lookup(uint32_t ino, const char *name, uint32_t *ino_p,
                uint8_t *type_p) {
  int error;

  if (name == NULL || !strlen(name))
    return EINVAL;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

  /* TODO */
  ext2_dirent_t dirent;
  uint32_t off_p = 0;

  if (EXT2_IFDIR != (inode.i_mode & EXT2_IFMT)) {
    return ENOTDIR;
  }

  while (ext2_readdir(ino, &off_p, &dirent)) {
    if (!strcmp(dirent.de_name, name)) {
      if (ino_p) {
        *ino_p = dirent.de_ino;
      }
      if (type_p) {
        *type_p = dirent.de_type;
      }
      return 0;
    }
  }

  return ENOENT;
}

/* Initializes ext2 filesystem stored in `fspath` file.
 * Returns 0 on success, otherwise an error. */
int ext2_mount(const char *fspath) {
  int error;

  if ((error = blk_init(fspath)))
    return error;

  /* Read superblock and verify we support filesystem's features. */
  ext2_superblock_t sb;
  ext2_read(0, &sb, EXT2_SBOFF, sizeof(ext2_superblock_t));

  debug(">>> super block\n"
        "# of inodes      : %d\n"
        "# of blocks      : %d\n"
        "block size       : %ld\n"
        "blocks per group : %d\n"
        "inodes per group : %d\n"
        "inode size       : %d\n",
        sb.sb_icount, sb.sb_bcount, 1024UL << sb.sb_log_bsize, sb.sb_bpg,
        sb.sb_ipg, sb.sb_inode_size);

  if (sb.sb_magic != EXT2_MAGIC)
    panic("'%s' cannot be identified as ext2 filesystem!", fspath);

  if (sb.sb_rev != EXT2_REV1)
    panic("Only ext2 revision 1 is supported!");

  size_t blksize = 1024UL << sb.sb_log_bsize;
  if (blksize != BLKSIZE)
    panic("ext2 filesystem with block size %ld not supported!", blksize);

  if (sb.sb_inode_size != sizeof(ext2_inode_t))
    panic("The only i-node size supported is %d!", sizeof(ext2_inode_t));

  /* Load interesting data from superblock into global variables.
   * Read group descriptor table into memory. */

  /* TODO */
  /* Set up blocks info. */
  block_count = sb.sb_bcount;
  blocks_per_group = sb.sb_bpg;

  group_desc_count = block_count / blocks_per_group;
  first_data_block = sb.sb_first_dblock;

  if (block_count % blocks_per_group != 0) {
    group_desc_count++;
  }

  /* Initialize group_desc and write to it from file. */
  group_desc = malloc(sizeof(ext2_groupdesc_t) * group_desc_count);
  ext2_read(0, group_desc, EXT2_GDOFF,
            group_desc_count * sizeof(ext2_groupdesc_t));

  /* Set up inodes info. */
  inode_count = sb.sb_icount;
  inodes_per_group = sb.sb_ipg;

  return 0;
}
