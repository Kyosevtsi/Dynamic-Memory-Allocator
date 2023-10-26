/**
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "sfmm.h"
#include <errno.h>

// defines
#define MIN_BLOCK_SIZE 32
#define ROW_SIZE 8

// global
static sf_block* prologue;
static sf_block* epilogue;

// functions
static void initialize_heap();
static size_t get_size(sf_block*);
static void set_footer(sf_block*);
static sf_block* skip_by_bytes(sf_block*, size_t);
static sf_block* skip_back_by_bytes(sf_block*, size_t);
static int find_freelist_index(size_t);
static void insert_into_freelist(sf_block*, int);
static int find_quicklist_index(size_t);
static sf_block* grab_from_quicklist(int);
static sf_block* search_in_freelist_index(size_t, int);
static void remove_from_freelist(sf_block*); 
static sf_block* split_block(size_t, sf_block*);
static void finalize_allocation(sf_block*);
static sf_block* get_previous_block_by_footer(sf_block*);
static int expand_heap();
static int check_validity(sf_block*);
static void insert_into_quicklist(sf_block*, int);
static void coalesce_quicklist(int);
static sf_block* coalesce_above(sf_block*);
static sf_block* coalesce_below(sf_block*);
static void coalesce_block(sf_block*);
static int size_power_of_two(size_t);

void *sf_malloc(size_t size) {
    // determine the size of the block needed
    // first check for valid size input
    if (size < 1) {
        return NULL;
    }
    size += ROW_SIZE;  // allocate additional 8 bytes for the header
    size = (size + 7) & (-ROW_SIZE);  // bitmask to get to the next 8 bytes
    if (size < MIN_BLOCK_SIZE) {  // min size = 32
        size = MIN_BLOCK_SIZE;
    }

    // make the heap if it doesn't exist
    if (sf_mem_start() == sf_mem_end()) {
        initialize_heap();
    }

    // search through the quick lists for a proper-sized block
    int quick_index = find_quicklist_index(size);
    if (quick_index < NUM_FREE_LISTS) {  // if index is valid
        if (sf_quick_lists[quick_index].length > 0) {
            sf_block* freeBlock = grab_from_quicklist(quick_index);
            finalize_allocation(freeBlock);
            return freeBlock->body.payload;
        }
    }

    // search through the main free list and split / expand if needed
    sf_block* freeBlock = NULL;
    while (freeBlock == NULL) {
        int index = find_freelist_index(size);  // find appropriate index for size
        for (; index < NUM_FREE_LISTS; index++) {
            sf_block* block = search_in_freelist_index(size, index);
            if (block != NULL) {
                freeBlock = block;
                break;
            }
        }

        // at this point: we either have a valid block or went through the whole freelist and haven't found one
        if (freeBlock) {
            // split it if no splinters
            if (get_size(freeBlock) - size <= MIN_BLOCK_SIZE) {  // easy case: can't split without splinters or split not needed
                finalize_allocation(freeBlock);  // set headers before return
                return freeBlock->body.payload;
            } else {  // split and reinsert the split block into the main freelist
                sf_block* split = split_block(size, freeBlock);
                finalize_allocation(freeBlock);
                int split_index = find_freelist_index(get_size(split));
                insert_into_freelist(split, split_index);
                return freeBlock->body.payload;
            }
        } else {
            // expand heap and coalesce
            int success = expand_heap();
            if (success == 1) {  // not successful
                sf_errno = ENOMEM;
                return NULL;
            }
        }
    }
    return NULL;  // if all else fails somehow
}

void sf_free(void *pp) {
    if (check_validity(pp) == 1) {  // invalid pointer
        abort();
    }
    sf_block* block = skip_back_by_bytes(pp, ROW_SIZE);  // go back by one row from payload -> header
    int quick_index = find_quicklist_index(get_size(block));
    if (quick_index < NUM_QUICK_LISTS) {  // block can fit within a quicklist
        insert_into_quicklist(block, quick_index);
    } else {  // too big to fit into a quicklist: insert into a main freelist
        block->header = block->header & ~(sf_header)1;  // set the block to free
        coalesce_block(block);
    }
}

void *sf_realloc(void *pp, size_t rsize) {
    if (check_validity(pp) == 1) {  // invalid pointer
        sf_errno = EINVAL;
        return NULL;
    }
    if (rsize == 0) {
        sf_free(pp);
        return NULL;
    }
    size_t total_rsize = rsize + ROW_SIZE;  // allocate additional 8 bytes for the header
    total_rsize = (total_rsize + 7) & (-ROW_SIZE);  // bitmask to get to the next 8 bytes
    sf_block* block = skip_back_by_bytes(pp, ROW_SIZE);  // go back by one row from payload -> header
    if (total_rsize < 32) {  // min block size = 32
        total_rsize = 32;
    }
    if (total_rsize == get_size(block)) {  // same sized block
        return block->body.payload;
    } else if (total_rsize > get_size(block)) {
        sf_block* new_block = sf_malloc(rsize);
        if (new_block == NULL) {
            return NULL;
        } else {
            new_block = skip_back_by_bytes(new_block, ROW_SIZE);  // skip back one row to the header
            memcpy(new_block->body.payload, block->body.payload, get_size(block) - ROW_SIZE);
            sf_free(pp);
            return new_block->body.payload;
        }
    } else {  // rsize < payload_size
        if (get_size(block) - total_rsize < 32) {  // making a split would cause a splinter
            return block->body.payload;
        }
        sf_block* newBlock = split_block(total_rsize, block);
        newBlock->header = newBlock->header | PREV_BLOCK_ALLOCATED;
        set_footer(newBlock);
        coalesce_block(newBlock);
        return block->body.payload;
    }
}

void *sf_memalign(size_t size, size_t align) {
    size_t check_align = align;
    if (check_align < ROW_SIZE) {
        sf_errno = EINVAL;
        return NULL;
    }
    if (size_power_of_two(check_align) == 0) {  // align is not a power of 2
        sf_errno = EINVAL;
        return NULL;
    }
    
    char* pp = sf_malloc(size + align + MIN_BLOCK_SIZE + ROW_SIZE);  // valid parameters: allocate bigger block than necessary
    sf_block* block = (sf_block*)(pp - ROW_SIZE);  // go back one row to get the block
    size_t padding = 0;
    while ((size_t)pp % align != 0) {  // get pp to the first aligned location
        pp += 1;  // move to the next byte in the payload
        padding += 1;
    }

    // at this point: pp is at an aligned byte, but we need to split off the block before it
    void* row_start = (void*)((size_t)pp & ~(size_t)7); // go to the start of pp's row
    while ((size_t)row_start - (size_t)block < (MIN_BLOCK_SIZE + ROW_SIZE)) { // get to a pointer far enough to be able to split the block (1 block + header before payload)
        pp += align;
        row_start = (void*)((size_t)pp & ~(size_t)7); // go to the start of pp's row
    }
    
    void* newBlock_start = (char*)row_start - ROW_SIZE;  // go back an additional row to where the new block would start
    size_t oldBlockSize = (char*)newBlock_start - (char*)block;
    sf_block* thisBlock = split_block(oldBlockSize, block);

    // from sf_free: free the old block
    int quick_index = find_quicklist_index(get_size(block));
    if (quick_index < NUM_QUICK_LISTS) {  // block can fit within a quicklist
        insert_into_quicklist(block, quick_index);
        thisBlock->header = thisBlock->header | PREV_BLOCK_ALLOCATED;
        set_footer(thisBlock);
    } else {  // too big to fit into a quicklist: insert into a main freelist
        block->header = block->header & ~(sf_header)1;  // set the block to free
        coalesce_block(block);
    }

    void* nextBlock_start = (void*)(((size_t)pp + size + 7) & (-ROW_SIZE));  // bitmask to get to where the next block's pointer is
    size_t thisBlock_total_size = (size_t)nextBlock_start - (size_t)thisBlock;
    if ((size_t)get_size(thisBlock) - thisBlock_total_size < MIN_BLOCK_SIZE) {  // if splitting would cause a splinter
        finalize_allocation(thisBlock);
        return pp;
    } else {  // split, free, coalsece
        sf_block* nextBlock = split_block((size_t)get_size(thisBlock) - thisBlock_total_size, thisBlock);

        // from sf_free: free the next block
        int quick_index = find_quicklist_index(get_size(nextBlock));
        if (quick_index < NUM_QUICK_LISTS) {  // block can fit within a quicklist
            insert_into_quicklist(nextBlock, quick_index);
        } else {  // too big to fit into a quicklist: insert into a main freelist
            nextBlock->header = nextBlock->header & ~(sf_header)1;  // set the block to free
            coalesce_block(nextBlock);
        }
        
        finalize_allocation(thisBlock);
        return pp;
    }
    return NULL;  // if all else fails return null
}

static void initialize_heap() {
    sf_mem_grow();
    prologue = ((sf_block*)sf_mem_start());  
    prologue->header = MIN_BLOCK_SIZE | THIS_BLOCK_ALLOCATED;  // block_size = 32, alloc = 1
    epilogue = ((sf_block*)(sf_mem_end() - ROW_SIZE));  // go back one row from the end for the epilogue
    epilogue->header = THIS_BLOCK_ALLOCATED;  // block_size = 0, alloc = 1  
        
    // initialize main free list
    int i;
    for (i = 0; i < NUM_FREE_LISTS; i++) {  // set sentinel nodes
        sf_free_list_heads[i].body.links.next = &sf_free_list_heads[i];
        sf_free_list_heads[i].body.links.prev = &sf_free_list_heads[i];
    }

    // add first free block to main freelist
    sf_block* firstFree = skip_by_bytes(prologue, MIN_BLOCK_SIZE);  // set address of first free block
    firstFree->header = (PAGE_SZ - MIN_BLOCK_SIZE - ROW_SIZE) | PREV_BLOCK_ALLOCATED;  // size = 4096 - 32(prologue) - 8(epilogue) + 2 (prev allocated)
    set_footer(firstFree);
    int index = find_freelist_index(get_size(firstFree));
    insert_into_freelist(firstFree, index);
}

static size_t get_size(sf_block *block) {
    size_t head = block->header;
    return (head >> 3) << 3;
}

static void set_footer(sf_block *block) {
    sf_footer* footer = (sf_footer*)((char*)block + get_size(block) - ROW_SIZE);
    *footer = block->header;
}

static sf_block* skip_by_bytes(sf_block* block, size_t bytes) {
    return (sf_block*)((char*)block + bytes);
}

static sf_block* skip_back_by_bytes(sf_block* block, size_t bytes) {
    return (sf_block*)((char*)block - bytes);
}

static int find_freelist_index(size_t size) {
    size_t max_size = MIN_BLOCK_SIZE;
    if (size == MIN_BLOCK_SIZE) {
        return 0;  // index 0 holds blocks of size 32
    }
    int i;
    for (i = 1; i < NUM_FREE_LISTS; i++) {
        max_size += max_size;
        if (size <= max_size) {
            return i;  // return first index where it fits
        }
    }
    return NUM_FREE_LISTS - 1;  // return highest index if size too large
}

static void insert_into_freelist(sf_block* block, int index) {
    sf_block* first_in_list = sf_free_list_heads[index].body.links.next;  // get first in list (might be sentinel)
    block->body.links.next = first_in_list;  // new block's next is the first in the list
    block->body.links.prev = &sf_free_list_heads[index];  // new block's prev is the sentinel 
    first_in_list->body.links.prev = block;  // first block's previous is the new block (first block can be sentinel)
    sf_free_list_heads[index].body.links.next = block;  // sentinel next is the new block
}

static int find_quicklist_index(size_t size) {
    size_t exact_size = size;
    if (size % 8 != 0) {
        return NUM_QUICK_LISTS;  // invalid index
    } else {
        return (exact_size - 32) / 8;
    }
}

static sf_block* grab_from_quicklist(int index) {
    sf_block* block = sf_quick_lists[index].first;  // get the first pointer in the list
    sf_quick_lists[index].length -= 1;  // reduce the length of the quick list
    sf_quick_lists[index].first = block->body.links.next;  // set the first of the quicklist to the extracted block's next
    return block;
}

static sf_block* search_in_freelist_index(size_t size, int index) {  // find and remove the right block from the freelist
    size_t min_size = size;
    sf_block* sentinel_address = &sf_free_list_heads[index];
    sf_block* block = sf_free_list_heads[index].body.links.next;
    while (block != sentinel_address) {
        if (get_size(block) >= min_size) {
            remove_from_freelist(block);
            return block;
        } else {
            block = block->body.links.next;
        }
    }
    return NULL;  // proper sized block not found in this index
}

static void remove_from_freelist(sf_block* block) {  // knowing the specific block, remove it from the freelist
    sf_block* previousBlock = block->body.links.prev;
    sf_block* nextBlock = block->body.links.next;
    previousBlock->body.links.next = nextBlock;  // the block before's next is now this block's next
    nextBlock->body.links.prev = previousBlock;  // the block after's previous is now this block's previous
    // block effectively removed from the free list
}

static sf_block* split_block(size_t size, sf_block* block) {  // returns pointer to the new split block
    sf_block* new_block = skip_by_bytes(block, size);
    size_t new_block_size = get_size(block) - size;
    new_block->header = (sf_header)new_block_size;
    set_footer(new_block);
    
    // update old block
    int states = block->header & 7;
    block->header = size + states;
    set_footer(block);

    return new_block;
}

static void finalize_allocation(sf_block* block) {
    block->header = block->header | THIS_BLOCK_ALLOCATED;
    sf_block* next_block_in_heap = skip_by_bytes(block, get_size(block));
    next_block_in_heap->header = next_block_in_heap->header | PREV_BLOCK_ALLOCATED;
    int allocated_bit = next_block_in_heap->header & THIS_BLOCK_ALLOCATED;  
    if (allocated_bit == 0) {  // set footer of next block if it is free
        set_footer(next_block_in_heap);
    }
}

static sf_block* get_previous_block_by_footer(sf_block* block) {  // PREVIOUS BLOCK MUST BE FREE (has a footer)
    sf_footer* previousFooter = (sf_footer*)skip_back_by_bytes(block, ROW_SIZE);
    size_t previousBlockSize = ((*previousFooter) >> 3) << 3;
    sf_block* previousBlock = skip_back_by_bytes(block, previousBlockSize);
    return previousBlock;
}

static int expand_heap() {
    sf_block* newpage = sf_mem_grow();  // newpage = &epilogue, sf_mem_end() = end of page
    if (newpage == NULL) {  // if more heap space could not be allocated
        return 1;
    }
    if ((epilogue->header & PREV_BLOCK_ALLOCATED) == 0) {  // if the block before epilogue is free coalesce
        sf_block* previousBlock = get_previous_block_by_footer(epilogue);
        remove_from_freelist(previousBlock);  // remove the previous block from the freelist to coalesce
        previousBlock->header += PAGE_SZ;  // size of the block increased by 4096 (still leaves the last row for the epilogue)
        set_footer(previousBlock);
        insert_into_freelist(previousBlock, find_freelist_index(get_size(previousBlock)));  // put the previous block back into the freelist
    } else {  // if block before the epilogue is allocated, then newpage should be made a free block
        newpage->header = (PAGE_SZ - ROW_SIZE) | PREV_BLOCK_ALLOCATED;  // set the header for the new page
        set_footer(newpage);
        insert_into_freelist(newpage, find_freelist_index(get_size(newpage)));
    }
    epilogue = ((sf_block*)(sf_mem_end() - ROW_SIZE));  // go back one row from the end for the epilogue
    epilogue->header = THIS_BLOCK_ALLOCATED;  // block_size = 0, alloc = 1  
    return 0;
}

static int check_validity(sf_block* pp) {  // pp is a pointer to the start of the payload (in a correct case)
    sf_block* block = skip_back_by_bytes(pp, ROW_SIZE);  // header of the block (thus start of block) is one row back from payload start
    if (!(pp == NULL)) {  // pp cannot be null
        if ((unsigned long)pp % 8 == 0) {  // pointer must be 8-byte aligned
            if (get_size(block) >= 32) {  // block must be at least minimum size
                if (get_size(block) % 8 == 0) {  // block size must be multiple of 8
                    if (block > prologue) {  // header of block must be after prologue
                        if (skip_by_bytes(block, get_size(block) - ROW_SIZE) < epilogue) {  // footer of block must be before epilogue
                            if ((block->header & THIS_BLOCK_ALLOCATED) == THIS_BLOCK_ALLOCATED) {  // block must be allocated
                                if ((block->header & IN_QUICK_LIST) == 0) {  // block must not be in quick list
                                    if ((block->header & PREV_BLOCK_ALLOCATED) == PREV_BLOCK_ALLOCATED) {
                                        return 0;
                                    } else {  // previous block is free: check to see if it actually is
                                        sf_footer* previousFooter = (sf_footer*)skip_back_by_bytes(block, ROW_SIZE);  // go back one row to the previous footer
                                        if (((*previousFooter) & THIS_BLOCK_ALLOCATED) == 0) {  // previous block is free
                                            return 0;  // valid
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return 1;  // invalid
}

static void insert_into_quicklist(sf_block* block, int index) {
    // set the block header properly
    block->header = block->header | IN_QUICK_LIST;  // block should already be allocated if it made it into the quicklist
    if (sf_quick_lists[index].length == 0) {
        sf_quick_lists[index].first = block;
        block->body.links.next = NULL;
        sf_quick_lists[index].length += 1;
    } else if (sf_quick_lists[index].length < QUICK_LIST_MAX) {  // block is not first, but there are <5 blocks on the list
        block->body.links.next = sf_quick_lists[index].first;
        sf_quick_lists[index].first = block;
        sf_quick_lists[index].length += 1;
    } else {  // there are 5 blocks on the list already
        coalesce_quicklist(index);
        // at this point: quicklist[index] is empty
        sf_quick_lists[index].first = block;
        block->body.links.next = NULL;
        sf_quick_lists[index].length += 1;
    }
}

static void coalesce_quicklist(int index) {
    while (sf_quick_lists[index].length > 0) {
        sf_block* block = sf_quick_lists[index].first;  // grab block from the front of the quick list
        sf_quick_lists[index].first = block->body.links.next;  // first element of the quick list is now the next block
        sf_quick_lists[index].length -= 1;  // subtract from the quick list length
        block->header = block->header & ~(sf_header)1; // block is no longer allocated 
        block->header = block->header & ~(sf_header)4; // block no longer in quick list
        if ((block->header & PREV_BLOCK_ALLOCATED) == 0) {  // if previous block is free
            block = coalesce_above(block);
        }
        sf_block* nextBlock = skip_by_bytes(block, get_size(block));
        if ((nextBlock->header & THIS_BLOCK_ALLOCATED) == 0) {  // if next block is free
            block = coalesce_below(block);
        } else {
            nextBlock->header = nextBlock->header & ~(sf_header)2;  // nextblock prev_alloc = 0
            set_footer(nextBlock);
        }
        insert_into_freelist(block, find_freelist_index(get_size(block)));  // insert block into freelist (fully coalesced)
    }
}

static sf_block* coalesce_above(sf_block* block) {  // block is free, previousBlock is free
    sf_block* previousBlock = get_previous_block_by_footer(block);  // go one row back to get the previous footer -> previous block
    remove_from_freelist(previousBlock);  // remove the previous block from the freelist
    previousBlock->header += get_size(block);
    set_footer(previousBlock);
    
    // from here: we have the new block, but we need to adjust the next block's prev_alloc
    sf_block* nextBlock = skip_by_bytes(previousBlock, get_size(previousBlock));  // since size of previous block = previous + block, this will go to next block
    nextBlock->header = nextBlock->header & ~(size_t)2;  // set prev_alloc to 0 in the next block b/c coalesced block is free
    set_footer(nextBlock);
    return previousBlock;
}

static sf_block* coalesce_below(sf_block* block) {
    sf_block* nextBlock = skip_by_bytes(block, get_size(block));  // skip to the next block
    remove_from_freelist(nextBlock);  // remove the next block from the freelist
    block->header += get_size(nextBlock);
    set_footer(block);
    return block;  // since we coalesced below, there should be no difference in the block after the next
}

static void coalesce_block(sf_block* block) {  // coalesce a freelist block
    if ((block->header & PREV_BLOCK_ALLOCATED) == 0) {  // if previous block is free
        block = coalesce_above(block);
    }
    sf_block* nextBlock = skip_by_bytes(block, get_size(block));
    if ((nextBlock->header & THIS_BLOCK_ALLOCATED) == 0) {  // if next block is free
        block = coalesce_below(block);
    } else {
        nextBlock->header = nextBlock->header & ~(sf_header)2;  // nextblock prev_alloc = 0
        set_footer(nextBlock);
    }
    insert_into_freelist(block, find_freelist_index(get_size(block)));  // insert block into freelist (fully coalesced)
}

static int size_power_of_two(size_t size) {
    // for power of two, must have binary following r = 0*10*
    size_t x = size;
    if (x) {
        while (x > 1) {
            if (x % 2 != 0) {
                return 0;
            } else {
                x = x / 2;
            }
        }
        return 1;  // success
    } else {
        return 0;  // x = 0
    }
}
