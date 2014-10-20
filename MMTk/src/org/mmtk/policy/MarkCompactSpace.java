/*
 *  This file is part of the Jikes RVM project (http://jikesrvm.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License. You
 *  may obtain a copy of the License at
 *
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  See the COPYRIGHT.txt file distributed with this work for information
 *  regarding copyright ownership.
 */
package org.mmtk.policy;

import java.util.ArrayList;

import org.mmtk.plan.TraceLocal;
import org.mmtk.plan.TransitiveClosure;
import org.mmtk.utility.Constants;
import org.mmtk.utility.Conversions;
import org.mmtk.utility.Log;
import org.mmtk.utility.alloc.Allocator;
import org.mmtk.utility.alloc.BumpPointer;
import org.mmtk.utility.alloc.EmbeddedMetaData;
import org.mmtk.utility.heap.FreeListPageResource;
import org.mmtk.utility.heap.Map;
import org.mmtk.utility.heap.VMRequest;
import org.mmtk.vm.Lock;
import org.mmtk.vm.VM;
import org.vmmagic.pragma.Inline;
import org.vmmagic.pragma.Uninterruptible;
import org.vmmagic.unboxed.Address;
import org.vmmagic.unboxed.Extent;
import org.vmmagic.unboxed.ObjectReference;
import org.vmmagic.unboxed.Offset;
import org.vmmagic.unboxed.Word;

/**
 * This class implements functionality for a simple sliding mark-compact
 * space.
 */
@Uninterruptible public final class MarkCompactSpace extends Space
  implements Constants {

  /****************************************************************************
   *
   * Class variables
   */

  /**
   * Select between using mark bits in a side bitmap, or mark bits
   * in the headers of object (or other sub-class scheme), and a single
   * mark bit per block.
   */
  public static final boolean HEADER_MARK_BITS = VM.config.MC_HEADER_MARK_BITS;

  private static final int OBJECT_LIVE_SHIFT = LOG_MIN_ALIGNMENT; // 4 byte resolution
  private static final int LOG_BIT_COVERAGE = OBJECT_LIVE_SHIFT;
  private static final int LOG_LIVE_COVERAGE = LOG_BIT_COVERAGE + LOG_BITS_IN_BYTE;
  private static final Word WORD_SHIFT_MASK = Word.one().lsh(LOG_BITS_IN_WORD).minus(Extent.one());

  public static final int SCALAR_HEADER_WORDS = 3;
  public static final int ARRAY_HEADER_WORDS = 4;
  public static final int SCALAR_HEADER_BYTES = SCALAR_HEADER_WORDS << LOG_BYTES_IN_WORD;
  public static final int ARRAY_HEADER_BYTES = ARRAY_HEADER_WORDS << LOG_BYTES_IN_WORD;

  public static final int LOG_LIVE_BYTES_PER_CHUNK = LOG_BYTES_IN_CHUNK - LOG_LIVE_COVERAGE;
  public static final int LIVE_BYTES_PER_CHUNK = 1 << LOG_LIVE_BYTES_PER_CHUNK; // Live bitmap
  public static final int HASH_BYTES_PER_CHUNK = LIVE_BYTES_PER_CHUNK; // Hash bitmap -- same space requirements as live bitmap
  public static final int ALIGNMENT_BYTES_PER_CHUNK = LIVE_BYTES_PER_CHUNK; // Alignment bitmap -- same space requirements as live bitmap
  public static final int BITMAP_BYTES_PER_CHUNK = LIVE_BYTES_PER_CHUNK + HASH_BYTES_PER_CHUNK + ALIGNMENT_BYTES_PER_CHUNK;

  public static final int BLOCK_SIZE = 512; // 256 Bytes = 64 Words of actual data -> 64 bits in bitmap = 2 words
  public static final int INITIAL_CHUNK_DATA_SIZE = (1 << LOG_BYTES_IN_CHUNK) - BITMAP_BYTES_PER_CHUNK;
  public static final int ADJUSTED_CHUNK_DATA_SIZE = (BLOCK_SIZE * INITIAL_CHUNK_DATA_SIZE) / (BLOCK_SIZE + BYTES_IN_ADDRESS);
  public static final int ADJUSTED_CHUNK_DATA_SIZE_ALIGNED = Conversions.pageAlign(ADJUSTED_CHUNK_DATA_SIZE);
  public static final int OFFSET_TABLE_SIZE = INITIAL_CHUNK_DATA_SIZE - ADJUSTED_CHUNK_DATA_SIZE_ALIGNED;
  public static final int OFFSET_TABLE_NUM_ENTRIES = OFFSET_TABLE_SIZE / BYTES_IN_ADDRESS;
  private static final Word BLOCK_MASK = Word.fromIntSignExtend(BLOCK_SIZE - 1);

  public static final int BYTES_PER_BITMAP_WORD = BYTES_IN_WORD << LOG_LIVE_COVERAGE;
  public static final int WORDS_PER_BITMAP_BLOCK = BLOCK_SIZE / BYTES_PER_BITMAP_WORD;
  public static final int BYTES_PER_DATA_WORD = BYTES_IN_WORD;
  public static final int WORDS_PER_DATA_BLOCK = BLOCK_SIZE / BYTES_PER_DATA_WORD;

  public static final int META_DATA_BYTES_PER_CHUNK = BITMAP_BYTES_PER_CHUNK + OFFSET_TABLE_SIZE;
  public static final Extent META_DATA_EXTENT_PER_CHUNK = Extent.fromIntSignExtend(META_DATA_BYTES_PER_CHUNK);
  protected static final int META_DATA_PAGES_PER_CHUNK = Conversions.bytesToPages(META_DATA_EXTENT_PER_CHUNK);

  private static final int HASH_OFFSET = LIVE_BYTES_PER_CHUNK;
  private static final int ALIGNMENT_OFFSET = HASH_OFFSET + HASH_BYTES_PER_CHUNK;

  /**
   *
   */
  public static final int LOCAL_GC_BITS_REQUIRED = 1;
  public static final int GLOBAL_GC_BITS_REQUIRED = 0;
  public static final int GC_HEADER_WORDS_REQUIRED = 1;

  private static final Word GC_MARK_BIT_MASK = Word.one();
  private static final Offset FORWARDING_POINTER_OFFSET = VM.objectModel.GC_HEADER_OFFSET();

  private static final Lock lock = VM.newLock("mcSpace");

  /** The list of occupied regions */
  private Address regionList = Address.zero();

  // TODO - maintain a separate list of partially allocated regions
  // for threads to allocate into immediately after a collection.

  /****************************************************************************
   *
   * Instance variables
   */

  /****************************************************************************
   *
   * Initialization
   */

  /**
   * The caller specifies the region of virtual memory to be used for
   * this space.  If this region conflicts with an existing space,
   * then the constructor will fail.
   *
   * @param name The name of this space (used when printing error messages etc)
   * @param vmRequest An object describing the virtual memory requested.
   */
  public MarkCompactSpace(String name, VMRequest vmRequest) {
    super(name, true, false, true, vmRequest);
    int totalMetadata = 0;
    if (!HEADER_MARK_BITS) {
      totalMetadata += (META_DATA_PAGES_PER_CHUNK);
    }
    if (vmRequest.isDiscontiguous()) {
      pr = new FreeListPageResource(this, totalMetadata);
    } else {
      pr = new FreeListPageResource(this, start, extent, totalMetadata);
    }
  }

  /**
   * Prepare for a new collection increment.
   *
   * @param clearBitmaps true if we should clear the live and hash bitmaps
   *        within the metadata area
   */
  public void prepare(boolean clearBitmaps) {
    if (!HEADER_MARK_BITS && clearBitmaps)
      zeroLiveBits();
  }

  /**
   * Release after a collection
   *
   * * @param clearBitmaps true if we should clear the live and hash bitmaps
   *        within the metadata area
   */
  public void release(boolean clearBitmaps) {
    if (!HEADER_MARK_BITS && clearBitmaps)
      zeroLiveBits();
  }


  /**
   * {@inheritDoc}<p>
   *
   * In this case we do nothing ecause we only release pages enmasse.
   */
  @Override
  @Inline
  public void release(Address start) {
    ((FreeListPageResource)pr).releasePages(start);
  }

  /**
   * Trace an object under a copying collection policy.
   * If the object is already copied, the copy is returned.
   * Otherwise, a copy is created and returned.
   * In either case, the object will be marked on return.
   *
   * @param trace The trace being conducted.
   * @param object The object to be forwarded.
   * @return The forwarded object.
   */
  @Override
  @Inline
  public ObjectReference traceObject(TransitiveClosure trace, ObjectReference object) {
    if (VM.VERIFY_ASSERTIONS)
      VM.assertions._assert(false);
    return null;
  }

  /**
   * Trace an object under a copying collection policy.
   * If the object is already copied, the copy is returned.
   * Otherwise, a copy is created and returned.
   * In either case, the object will be marked on return.
   *
   * @param trace The trace being conducted.
   * @param object The object to be forwarded.
   * @return The forwarded object.
   */
  @Inline
  public ObjectReference traceMarkObject(TraceLocal trace, ObjectReference object) {
    if (MarkCompactCollector.VERY_VERBOSE) {
      Log.write("marking "); Log.write(object);
    }
    boolean initiallyUnmarked = false;
    if (HEADER_MARK_BITS)
      initiallyUnmarked = testAndMark(object);
    else
      initiallyUnmarked = testAndSetLiveBits(object);

    if (initiallyUnmarked) {
      trace.processNode(object);
    } else if (!getForwardingPointer(object).isNull()) {
      if (MarkCompactCollector.VERY_VERBOSE) {
        Log.write(" -> "); Log.writeln(getForwardingPointer(object));
      }
      return getForwardingPointer(object);
    }
    if (MarkCompactCollector.VERY_VERBOSE) {
      Log.writeln();
    }
    return object;
  }

  /**
   * Trace an object under a copying collection policy.
   * If the object is already copied, the copy is returned.
   * Otherwise, a copy is created and returned.
   * In either case, the object will be marked on return.
   *
   * @param trace The trace being conducted.
   * @param object The object to be forwarded.
   * @return The forwarded object.
   */
  @Inline
  public ObjectReference traceForwardObject(TraceLocal trace, ObjectReference object) {
    boolean initiallyMarked = false;
    if (HEADER_MARK_BITS)
      initiallyMarked = testAndClearMark(object);
    else
      initiallyMarked = testAndClearLiveBits(object);

    if (initiallyMarked) {
      trace.processNode(object);
    }
    ObjectReference newObject = getForwardingPointer(object);
    if (MarkCompactCollector.VERY_VERBOSE) {
      Log.write("forwarding "); Log.write(object);
      Log.write(" -> "); Log.writeln(newObject);
    }
    if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(!newObject.isNull());
    return getForwardingPointer(object);
  }

  @Override
  public boolean isLive(ObjectReference object) {
    return isMarked(object);
  }

  @Override
  public boolean isReachable(ObjectReference object) {
    return isMarked(object);
  }

  /**
   * Stores the given forwarding address in the offset table
   *
   * @param blockNumber The block number in which to store the address.
   * @param address     The forwarding address to be stored
   */
  public static void storeOffsetTableFwdAddr(int blockNumber, Address address, Address metaDataBase, boolean overwrite) {
    Address block = offsetTableBlockAddress(metaDataBase, blockNumber);
    if (!overwrite && !block.loadAddress().isZero()) {
      return;
    }
    block.store(address);
  }

  public static Address getOffsetTableFwdAddr(int blockNumber, Address address, Address metaDataBase) {
    Address block = offsetTableBlockAddress(metaDataBase, blockNumber);
    Address ret = block.loadAddress();
    return ret;
  }

  /**
   * Returns the address of the location corresponding to the given block number passed
   *
   * @param block         The block number for which the address is required
   * @param metaDataBase  Metadata base address
   */
  private static Address offsetTableBlockAddress(Address metaDataBase, int block) {
    int blockOffset = block << LOG_BYTES_IN_WORD;
    Address offsetTableBase = metaDataBase.plus(BITMAP_BYTES_PER_CHUNK);
    return offsetTableBase.plus(blockOffset);
  }

  /**
   * Gets the block number for a given object
   *
   * @param address The address of the object
   */
  public static int getBlockNumber(Address address) {
    Address base = EmbeddedMetaData.getMetaDataBase(address).plus(META_DATA_EXTENT_PER_CHUNK);
    return address.diff(base).toInt() / BLOCK_SIZE;
  }

  public static Address getBlockAddress(Address objAddress) {
    return objAddress.toWord().and(BLOCK_MASK.not()).toAddress();
  }

  public static Address getNewAddress(ObjectReference object, boolean verbose) {
    Address fromObjStart = VM.objectModel.objectStartRef(object);
    Address fromObjEnd = getObjectEndAddress(object);
    Address fromBlockStartAddress = getBlockAddress(fromObjStart);
    Address fromBlockEndAddress = fromBlockStartAddress.plus(BLOCK_SIZE);

    Address metaDataBase = EmbeddedMetaData.getMetaDataBase(fromObjStart);
    int objectSize = fromObjEnd.diff(fromObjStart).toInt() + BYTES_IN_WORD;
    int objectAlignment = MarkCompactSpace.getObjectAlignmentFromBitmap(object);
    int objectOffset = MarkCompactSpace.getObjectOffsetFromBitmap(object);
    boolean objectHashed = MarkCompactSpace.hashBitSet(object);
    int reservedSize = objectSize;
    if (objectHashed)
      reservedSize += BYTES_IN_WORD;

    int blockNumber = getBlockNumber(fromObjStart);
    verbose = false;
    Address toBlockBaseAddress = getOffsetTableFwdAddr(blockNumber, fromBlockStartAddress, metaDataBase);

    if (verbose) {
      Log.writeln("**********************************************************************");
      Log.write("objAddress: "); Log.write(fromObjStart);
      Log.write(". metaDataBase: "); Log.write(metaDataBase);
      Log.write(". toBlockBaseAddr: "); Log.writeln(toBlockBaseAddress);
      Log.write("blockNumber: "); Log.write(blockNumber);
      Log.write(". fromBlockStart: "); Log.write(fromBlockStartAddress);
      Log.write(". fromBlockEnd: "); Log.writeln(fromBlockEndAddress);
    }

    Address regionBase = MarkCompactLocal.getRegionBase(toBlockBaseAddress);
    Address regionLimit = MarkCompactLocal.getRegionLimit(regionBase);
    Address regionDataStart = MarkCompactLocal.getDataStart(regionBase);

    Address cursor = toBlockBaseAddress;
    if (cursor.LT(regionDataStart)){
      cursor = cursor.plus(MarkCompactLocal.DATA_START_OFFSET);
    }

    // get total size of live data between block start and object start
    Address bitmapBlockStart = getLiveWordAddress(fromBlockStartAddress);
    int wordsBeforeObject = fromObjStart.diff(fromBlockStartAddress).toInt() >> LOG_BYTES_IN_WORD;

    Address current = bitmapBlockStart;
    Word mask = Word.one();
    int ticker = 0;
    int objectStartTick = 0;
    int offset = 0;
    int align = BYTES_IN_WORD;

    boolean isLive = false;
    boolean isHashed = false;
    boolean isDoubleAligned = false;
    boolean ignoreFirstLiveBit = false;
    boolean startMarker = true;

    // Do a first pass through block to determine number of live bits in total
    int numLiveBits = getTotalLiveBits(bitmapBlockStart, wordsBeforeObject);
    if (numLiveBits % 2 != 0) {
      // We have an odd number of live marks. Therefore, the first one is likely
      // to be the end marker of an object from the previous block. We must
      // ignore this marked bit before proceeding
      ignoreFirstLiveBit = true;
    }

    if (verbose) {
      Log.write("regionBase: "); Log.write(regionBase);
      Log.write(". regionLimit: "); Log.write(regionLimit);
      Log.write(". regionDataStart: "); Log.writeln(regionDataStart);
      Log.write("bitmapBlockStartAddr: "); Log.write(bitmapBlockStart);
      Log.write(". wordsBeforeObject: "); Log.write(wordsBeforeObject);
      Log.write(". numLiveBits: "); Log.writeln(numLiveBits);
    }

    while(ticker < wordsBeforeObject) {
      Word value = current.loadWord();
      isLive = value.and(mask).EQ(mask);

      if (isLive) {
        if (ignoreFirstLiveBit) {
          ignoreFirstLiveBit = false;
        } else {
          // normal path
          if (startMarker) {
            // start bit
            // First get the ticker value to mark beginning of object
            objectStartTick = ticker;

            // Check hash bit value
            Word hashValue = current.plus(HASH_OFFSET).loadWord();
            isHashed = hashValue.and(mask).EQ(mask);

            // Get alignment value
            Word alignValue = current.plus(ALIGNMENT_OFFSET).loadWord();
            isDoubleAligned = alignValue.and(mask).EQ(mask);
            align = (isDoubleAligned ? 2 : 1) * BYTES_IN_WORD;

          } else {
            // end bit
            // First get offset requirement
            Word offsetStatus = current.plus(HASH_OFFSET).loadWord();
            if (offsetStatus.and(mask).EQ(mask)) {
              Word offsetType = current.plus(ALIGNMENT_OFFSET).loadWord();
              boolean isArray = offsetType.and(mask).EQ(mask);
              offset = isArray ? ARRAY_HEADER_BYTES : SCALAR_HEADER_BYTES;
            } else {
              offset = 0;
            }

            // Align cursor appropriately
            cursor = Allocator.alignAllocationNoFill(cursor, align, offset);

            // Add single word to object size if it has been hashed
            int size = (ticker - objectStartTick + 1) << Constants.LOG_BYTES_IN_WORD;
            size += (isHashed) ? BYTES_IN_WORD : 0;

            Address testCursor = cursor.plus(size);
            Address alignedTestCursor = Allocator.alignAllocationNoFill(testCursor, align, offset);
            if (!alignedTestCursor.LE(regionLimit)) {
              regionBase = MarkCompactLocal.getNextRegion(regionBase);
              regionLimit = MarkCompactLocal.getRegionLimit(regionBase);
              cursor = MarkCompactLocal.getDataStart(regionBase);

              // Re-align cursor appropriately
              cursor = Allocator.alignAllocationNoFill(cursor, align, offset);
            }

            cursor = cursor.plus(size);
          }
          startMarker = !startMarker;
        }
      }

      mask = mask.lsh(1);
      if (mask.EQ(Word.zero())) {
        mask = Word.one();
        current = current.plus(BYTES_IN_WORD);
      }

      ticker++;
    }

    // Test if adding object size to cursor moves us beyond region limit
    // If so, then move cursor into next region
    Address testCursor = cursor.plus(reservedSize);
    Address alignedTestCursor = Allocator.alignAllocationNoFill(testCursor, objectAlignment, objectOffset);
    if (!alignedTestCursor.LE(regionLimit)) {
      regionBase = MarkCompactLocal.getNextRegion(regionBase);
      regionLimit = MarkCompactLocal.getRegionLimit(regionBase);
      cursor = MarkCompactLocal.getDataStart(regionBase);
    }

    // Re-align cursor appropriately
    cursor = Allocator.alignAllocationNoFill(cursor, objectAlignment, objectOffset);
    if (verbose) {
      Log.write("finalAddress: "); Log.write(cursor);
      Log.write(". Align: "); Log.write(objectAlignment);
      Log.write(". Offset: "); Log.write(objectOffset);
      Log.write(". Hashed: "); Log.write(objectHashed);
      Log.write(". reservedSize: "); Log.writeln(reservedSize);
    }
    if (regionBase.EQ(MarkCompactLocal.getRegionBase(fromObjStart)) && cursor.GT(fromObjStart)) {
      // If corrected address is an offset table address, replace stored address with correct one
      if (cursor.EQ(toBlockBaseAddress)) {
        if (verbose) {
          Log.writeln("Replacing stored forwarding address");
        }
        storeOffsetTableFwdAddr(blockNumber, fromObjStart, metaDataBase, true);
      }

      // Ensure forwarding address does not lead object address if they are in same region
      cursor = fromObjStart;

      if (verbose) {
        Log.write("finalAddress after adjustment: "); Log.writeln(cursor);
      }
    }

    return cursor;
  }

  private static int getTotalLiveBits(Address start, int limit) {
    int ticker = 0;
    int liveBits = 0;
    Word mask = Word.one();
    boolean isLive = false;
    Address current = start;

    while(ticker < limit) {
      Word value = current.loadWord();
      isLive = value.and(mask).EQ(mask);

      if (isLive) {
        liveBits++;
      }

      mask = mask.lsh(1);
      if (mask.EQ(Word.zero())) {
        mask = Word.one();
        current = current.plus(BYTES_IN_WORD);
      }

      ticker++;
    }

    return liveBits;
  }

  public static int getTotalLiveBits(Address start, Address end) {
    int liveBits = 0;
    Word mask = Word.one();
    boolean isLive = false;
    Address current = start;

    while(current.LE(end)) {
      Word value = current.loadWord();
      isLive = value.and(mask).EQ(mask);

      if (isLive) {
        liveBits++;
      }

      mask = mask.lsh(1);
      if (mask.EQ(Word.zero())) {
        mask = Word.one();
        current = current.plus(BYTES_IN_WORD);
      }

    }

    return liveBits;
  }


  /****************************************************************************
   *
   * Header manipulation
   */

  /**
   * Perform any required post-allocation initialization
   *
   * <i>Nothing to be done in this case</i>
   *
   * @param object the object ref to the storage to be initialized
   */
  @Inline
  public void postAlloc(ObjectReference object) {
  }

  /**
   * Non-atomic read of forwarding pointer
   *
   * @param object The object whose forwarding pointer is to be read
   * @return The forwarding pointer stored in <code>object</code>'s
   * header.
   */
  @Inline
  public static ObjectReference getForwardingPointer(ObjectReference object) {
    return object.toAddress().loadObjectReference(FORWARDING_POINTER_OFFSET);
  }

  /**
   * Initialise the header of the object.
   *
   * @param object The object to initialise
   */
  @Inline
  public void initializeHeader(ObjectReference object) {
    // nothing to do
  }

  /**
   * Used to mark boot image objects during a parallel scan of objects
   * during GC.
   *
   * @param object The object to be marked
   * @return {@code true} if marking was done.
   */
  @Inline
  public static boolean testAndMark(ObjectReference object) {
    Word oldValue;
    do {
      oldValue = VM.objectModel.prepareAvailableBits(object);
      Word markBit = oldValue.and(GC_MARK_BIT_MASK);
      if (!markBit.isZero()) return false;
    } while (!VM.objectModel.attemptAvailableBits(object, oldValue,
                                                oldValue.or(GC_MARK_BIT_MASK)));
    return true;
  }

  /**
   * Used to mark boot image objects during a parallel scan of objects
   * during GC Returns true if marking was done.
   *
   * @param object The object to be marked
   */
  @Inline
  public static boolean isMarked(ObjectReference object) {
    if (HEADER_MARK_BITS) {
      Word oldValue = VM.objectModel.readAvailableBitsWord(object);
      Word markBit = oldValue.and(GC_MARK_BIT_MASK);
      return (!markBit.isZero());
    } else {
      return liveBitsSet(object);
    }
  }

  /**
   * Used to mark boot image objects during a parallel scan of objects
   * during GC Returns true if marking was done.
   *
   * @param object The object to be marked
   */
  @Inline
  private static boolean testAndClearMark(ObjectReference object) {
    Word oldValue;
    do {
      oldValue = VM.objectModel.prepareAvailableBits(object);
      Word markBit = oldValue.and(GC_MARK_BIT_MASK);
      if (markBit.isZero()) return false;
    } while (!VM.objectModel.attemptAvailableBits(object, oldValue,
                                                oldValue.and(GC_MARK_BIT_MASK.not())));
    return true;
  }


  /**
   * Used to mark boot image objects during a parallel scan of objects
   * during GC Returns true if marking was done.
   *
   * @param object The object to be marked
   */
  @Inline
  public static boolean toBeCompacted(ObjectReference object) {
    return isMarked(object) && getForwardingPointer(object).isNull();
  }

  /**
   * Used to mark boot image objects during a parallel scan of objects
   * during GC Returns true if marking was done.
   *
   * @param object The object to be marked
   */
  @Inline
  public static void clearMark(ObjectReference object) {
    Word oldValue = VM.objectModel.readAvailableBitsWord(object);
    VM.objectModel.writeAvailableBitsWord(object, oldValue.and(GC_MARK_BIT_MASK.not()));
  }

  /**
   * Non-atomic write of forwarding pointer word (assumption, thread
   * doing the set has done attempt to forward and owns the right to
   * copy the object)
   *
   * @param object The object whose forwarding pointer is to be set
   * @param ptr The forwarding pointer to be stored in the object's
   * forwarding word
   */
  @Inline
  public static void setForwardingPointer(ObjectReference object,
                                           ObjectReference ptr) {
    object.toAddress().store(ptr.toAddress(), FORWARDING_POINTER_OFFSET);
  }

  /**
   * Non-atomic clear of forwarding pointer word (assumption, thread
   * doing the set has done attempt to forward and owns the right to
   * copy the object)
   *
   * @param object The object whose forwarding pointer is to be set
   */
  @Inline
  public static void clearForwardingPointer(ObjectReference object) {
    object.toAddress().store(Address.zero(), FORWARDING_POINTER_OFFSET);
  }

  /**
   * @return A region of this space that has net yet been compacted during
   *   the current collection
   */
  public Address getNextRegion() {
    lock.acquire();
    if (regionList.isZero()) {
      lock.release();
      return Address.zero();
    }
    Address result = regionList;
    regionList = BumpPointer.getNextRegion(regionList);
    BumpPointer.clearNextRegion(result);
    lock.release();
    return result;
  }

  /**
   * Append a region or list of regions to the global list
   * @param region
   */
  public void append(Address region) {
    lock.acquire();
    if (MarkCompactCollector.VERBOSE) {
      Log.write("Appending region "); Log.write(region);
      Log.writeln(" to global list");
    }
    if (regionList.isZero()) {
      regionList = region;
    } else {
      appendRegion(regionList,region);
    }
    lock.release();
  }

  public static void appendRegion(Address listHead, Address region) {
    if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(!listHead.isZero());
    if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(!region.isZero());
    Address cursor = listHead;
    while (!BumpPointer.getNextRegion(cursor).isZero()) {
      cursor = BumpPointer.getNextRegion(cursor);
    }
    BumpPointer.setNextRegion(cursor,region);
  }

  /****************************************************************************
   *
   * Live bit manipulation
   */

  /**
   * Atomically set the live bit for a given object
   *
   * @param object The object whose live bit is to be set.
   * @return {@code true} if the bit was changed to true.
   */
  @Inline
  public static boolean testAndSetLiveBit(ObjectReference object) {
    return updateLiveBit(VM.objectModel.objectStartRef(object), true, true);
  }

  /**
   * Atomically set the live bits for a given object
   * These correspond to the first and last words of the object
   *
   * @param object The object whose live bits are to be set.
   * @return {@code true} if the bits were changed to true.
   */
  @Inline
  public static boolean testAndSetLiveBits(ObjectReference object) {
    Address objectStartAddress = VM.objectModel.objectStartRef(object);
    Address objectEndAddress = getObjectEndAddress(object);

    boolean objectStartUpdated = updateLiveBit(objectStartAddress, true, true);
    updateLiveBit(objectEndAddress, true, true);

    if (VM.objectModel.isHashed(object)) {
      updateHashBit(objectStartAddress, true, true);
    } else {
      updateHashBit(objectStartAddress, false, true);
    }

    if (VM.objectModel.getAlignWhenCopied(object) == (2 * Constants.BYTES_IN_WORD)) {
      updateAlignmentBit(objectStartAddress, true, true);
    } else {
      updateAlignmentBit(objectStartAddress, false, true);
    }

    // We use a secondary bit in the hash bit vector to indicate whether the offset is non-zero
    // A non-zero offset mean that we will use a secondary bit in the align bit vector to
    // indicate whether the object is a scalar or an array.
    int offset = VM.objectModel.getAlignOffsetWhenCopied(object);
    if (offset == SCALAR_HEADER_BYTES) {
      // Switch on offset status and set offsetValue to scalar, which in this case is a no-op
      updateHashBit(objectEndAddress, true, true);
    } else if (offset == ARRAY_HEADER_BYTES) {
      // Switch on offset status and set offsetValue to array, by flipping bit on
      updateHashBit(objectEndAddress, true, true);
      updateAlignmentBit(objectEndAddress, true, true);
    }

    if (VM.VERIFY_ASSERTIONS) {
      VM.assertions._assert(liveBitSet(objectStartAddress));
      VM.assertions._assert(liveBitSet(objectEndAddress));
    }

    return objectStartUpdated;
  }

  /**
   * Atomically clear the live bit for a given object
   *
   * @param object The object whose live bit is to be cleared.
   * @return {@code true} if the bit was changed to false.
   */
  @Inline
  public static boolean testAndClearLiveBit(ObjectReference object) {
    return updateLiveBit(VM.objectModel.objectStartRef(object), false, true);
  }

  /**
   * Atomically clear the live bits for a given object
   *
   * @param object The object whose live bits are to be cleared.
   * @return {@code true} if the bits were changed to false.
   */
  @Inline
  public static boolean testAndClearLiveBits(ObjectReference object) {
    Address objectStartAddress = VM.objectModel.objectStartRef(object);
    Address objectEndAddress = getObjectEndAddress(object);

    boolean objectStartUpdated = updateLiveBit(objectStartAddress, false, true);
    updateLiveBit(objectEndAddress, false, true);

    if (VM.VERIFY_ASSERTIONS) {
      VM.assertions._assert(!liveBitSet(objectStartAddress));
      VM.assertions._assert(!liveBitSet(objectEndAddress));
    }

    return objectStartUpdated;
  }

  /**
   * Set the live bit for a given address
   *
   * @param address The address whose live bit is to be set.
   * @param set {@code true} if the bit is to be set, as opposed to cleared
   * @param atomic {@code true} if we want to perform this operation atomically
   *
   * @return {@code true} if the bit was changed.
   */
  @Inline
  private static boolean updateLiveBit(Address address, boolean set, boolean atomic) {
    Word oldValue, newValue;
    Address liveWord = getLiveWordAddress(address);

    Word mask = getMask(address, true);
    if (atomic) {
      do {
        oldValue = liveWord.prepareWord();
        newValue = (set) ? oldValue.or(mask) : oldValue.and(mask.not());
      } while (!liveWord.attempt(oldValue, newValue));
    } else {
      oldValue = liveWord.loadWord();
      liveWord.store(set ? oldValue.or(mask) : oldValue.and(mask.not()));
    }
    if (set) {
      return oldValue.and(mask).NE(mask);
    } else {
      return oldValue.or(mask.not()).NE(mask.not());
    }
  }

  /**
   * Set the hash bit for a given address
   *
   * @param address The address whose hash bit is to be set.
   * @param set {@code true} if the bit is to be set, as opposed to cleared
   * @param atomic {@code true} if we want to perform this operation atomically
   *
   * @return {@code true} if the bit was changed.
   */
  @Inline
  private static boolean updateHashBit(Address address, boolean set, boolean atomic) {
    Word oldValue, newValue;
    Address liveWord = getLiveWordAddress(address);
    Address hashWord = liveWord.plus(LIVE_BYTES_PER_CHUNK); // advance by extent of live bitmap

    Word mask = getMask(address, true);
    if (atomic) {
      do {
        oldValue = hashWord.prepareWord();
        newValue = (set) ? oldValue.or(mask) : oldValue.and(mask.not());
      } while (!hashWord.attempt(oldValue, newValue));
    } else {
      oldValue = hashWord.loadWord();
      hashWord.store(set ? oldValue.or(mask) : oldValue.and(mask.not()));
    }
    if (set) {
      return oldValue.and(mask).NE(mask);
    } else {
      return oldValue.or(mask.not()).NE(mask.not());
    }
  }

  /**
   * Set the double-alignment bit for a given address
   *
   * @param address The address whose alignment bit is to be set.
   * @param set {@code true} if the bit is to be set, as opposed to cleared
   * @param atomic {@code true} if we want to perform this operation atomically
   *
   * @return {@code true} if the bit was changed.
   */
  @Inline
  private static boolean updateAlignmentBit(Address address, boolean set, boolean atomic) {
    Word oldValue, newValue;
    Address liveWord = getLiveWordAddress(address);
    Address hashWord = liveWord.plus(LIVE_BYTES_PER_CHUNK + ALIGNMENT_BYTES_PER_CHUNK); // advance by extent of live+alignment bitmap

    Word mask = getMask(address, true);
    if (atomic) {
      do {
        oldValue = hashWord.prepareWord();
        newValue = (set) ? oldValue.or(mask) : oldValue.and(mask.not());
      } while (!hashWord.attempt(oldValue, newValue));
    } else {
      oldValue = hashWord.loadWord();
      hashWord.store(set ? oldValue.or(mask) : oldValue.and(mask.not()));
    }
    if (set) {
      return oldValue.and(mask).NE(mask);
    } else {
      return oldValue.or(mask.not()).NE(mask.not());
    }
  }

  /**
   * Calculate the size of an object using its mark bits
   * @param object The Object
   */
  public static int getObjectSizeFromBitmap(ObjectReference object) {
    Address objectStartAddress = VM.objectModel.objectStartRef(object);

    Address actualObjAddress = objectStartAddress.plus(BYTES_IN_WORD);
    Address liveWordAddress = getLiveWordAddress(actualObjAddress);
    Word mask = getMask(actualObjAddress, true);

    Address metadataStart = EmbeddedMetaData.getMetaDataBase(actualObjAddress);
    Address metadataEnd = metadataStart.plus(LIVE_BYTES_PER_CHUNK);

    boolean isLive = false;
    int count = 1;

    while (!isLive) {
      if (VM.VERIFY_ASSERTIONS)
        VM.assertions._assert(liveWordAddress.LE(metadataEnd));

      Word liveWord = liveWordAddress.loadWord();
      isLive = liveWord.and(mask).EQ(mask);

      mask = mask.lsh(1);
      if (mask.EQ(Word.zero())) {
        mask = Word.one();
        liveWordAddress = liveWordAddress.plus(BYTES_IN_WORD);
      }

      count++;
    }

    return (count << LOG_BYTES_IN_WORD);
  }

  /**
   * Return the alignment requirement for the object passed
   * @param object The Object
   */
  public static int getObjectAlignmentFromBitmap(ObjectReference object) {
    boolean doubleAligned = alignmentBitSet(VM.objectModel.objectStartRef(object));
    return (doubleAligned ? 2 : 1) * Constants.BYTES_IN_WORD;
  }

  /**
   * Return the alignment offset requirements for a copy of this object
   * @param object The Object
   */
  public static int getObjectOffsetFromBitmap(ObjectReference object) {
    Address objectEndAddress = getObjectEndAddress(object);
    if (hashBitSet(objectEndAddress)) {
      return alignmentBitSet(objectEndAddress) ? ARRAY_HEADER_BYTES : SCALAR_HEADER_BYTES;
    } else {
      return 0;
    }
  }

  /**
   * Test the live bit for a given object
   *
   * @param object The object whose live bit is to be set.
   */
  @Inline
  protected static boolean liveBitSet(ObjectReference object) {
    return liveBitSet(VM.objectModel.objectStartRef(object));
  }

  /**
   * Test the hash bit for a given object
   *
   * @param object The object whose hash bit is to be tested.
   */
  @Inline
  protected static boolean hashBitSet(ObjectReference object) {
    return hashBitSet(VM.objectModel.objectStartRef(object));
  }

  /**
   * Test the live bits (first and last) for a given object
   *
   * @param object The object
   */
  @Inline
  protected static boolean liveBitsSet(ObjectReference object) {
    Address objectStartAddress = VM.objectModel.objectStartRef(object);
    Address objectEndAddress = getObjectEndAddress(object);

    boolean startSet = liveBitSet(objectStartAddress);
    boolean endSet = liveBitSet(objectEndAddress);

    if (VM.VERIFY_ASSERTIONS)
      VM.assertions._assert(startSet == endSet);

    return startSet && endSet;
  }

  /**
   * Test the live bit for a given address
   *
   * @param address The address whose live bit is to be tested.
   * @return {@code true} if the live bit for this address is set.
   */
  @Inline
  protected static boolean liveBitSet(Address address) {
    Address liveWord = getLiveWordAddress(address);
    Word mask = getMask(address, true);
    Word value = liveWord.loadWord();
    return value.and(mask).EQ(mask);
  }

  /**
   * Test the hash bit for a given address
   *
   * @param address The address whose hash bit is to be tested.
   * @return {@code true} if the hash bit for this address is set.
   */
  @Inline
  protected static boolean hashBitSet(Address address) {
    Address liveWord = getLiveWordAddress(address);
    Address hashWord = liveWord.plus(LIVE_BYTES_PER_CHUNK); // advance by extent of live bitmap
    Word mask = getMask(address, true);
    Word value = hashWord.loadWord();
    return value.and(mask).EQ(mask);
  }

  /**
   * Test the alignment bit for a given address
   *
   * @param address The address whose alignment bit is to be tested.
   * @return {@code true} if the hash bit for this address is set.
   */
  @Inline
  protected static boolean alignmentBitSet(Address address) {
    Address liveWord = getLiveWordAddress(address);
    Address hashWord = liveWord.plus(LIVE_BYTES_PER_CHUNK + ALIGNMENT_BYTES_PER_CHUNK); // advance by extent of live + alignment bitmap
    Word mask = getMask(address, true);
    Word value = hashWord.loadWord();
    return value.and(mask).EQ(mask);
  }

  /**
   * Clear the live bit for a given object
   *
   * @param object The object whose live bit is to be cleared.
   */
  @Inline
  protected static void clearLiveBit(ObjectReference object) {
    clearLiveBit(VM.objectModel.objectStartRef(object));
  }

  /**
   * Clear the live bit for a given address
   *
   * @param address The address whose live bit is to be cleared.
   */
  @Inline
  protected static void clearLiveBit(Address address) {
    updateLiveBit(address, false, true);
  }

  protected void zeroLiveBits() {
   if (contiguous) {
      Address end = ((FreeListPageResource)pr).getHighWater();
      Address cursor = start;
      while (cursor.LT(end)) {
        Address metadata = EmbeddedMetaData.getMetaDataBase(cursor);
        VM.memory.zero(false, metadata, META_DATA_EXTENT_PER_CHUNK);
        cursor = cursor.plus(EmbeddedMetaData.BYTES_IN_REGION);
      }
    } else {
      for(Address cursor = headDiscontiguousRegion; !cursor.isZero(); cursor = Map.getNextContiguousRegion(cursor)) {
        Address metadata = EmbeddedMetaData.getMetaDataBase(cursor);
        VM.memory.zero(false, metadata, META_DATA_EXTENT_PER_CHUNK);
      }
    }
  }

  /**
   * Given an address, produce a bit mask for the live table
   *
   * @param address The address whose live bit mask is to be established
   * @param set True if we want the mask for <i>setting</i> the bit, false if we
   *          want the mask for <i>clearing</i> the bit.
   * @return The appropriate bit mask for object for the live table for.
   */
  @Inline
  public static Word getMask(Address address, boolean set) {
    int shift = address.toWord().rshl(OBJECT_LIVE_SHIFT).and(WORD_SHIFT_MASK).toInt();
    Word rtn = Word.one().lsh(shift);
    return (set) ? rtn : rtn.not();
  }

  /**
   * Given an address, return the address of the live word for that address.
   *
   * @param address The address whose live word address is to be returned
   * @return The address of the live word for this object
   */
  @Inline
  public static Address getLiveWordAddress(Address address) {
    Address rtn = EmbeddedMetaData.getMetaDataBase(address);
    return rtn.plus(EmbeddedMetaData.getMetaDataOffset(address,
        LOG_LIVE_COVERAGE, LOG_BYTES_IN_WORD));
  }

  private static Address getObjectEndAddress(ObjectReference object) {
    int size = VM.objectModel.getCurrentSize(object);
    return VM.objectModel.objectStartRef(object).plus(size).minus(BYTES_IN_WORD);
  }

}
