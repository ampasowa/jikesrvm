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

import org.mmtk.plan.TraceLocal;
import org.mmtk.plan.TransitiveClosure;
import org.mmtk.utility.Constants;
import org.mmtk.utility.Conversions;
import org.mmtk.utility.Log;
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

  public static final int LOG_LIVE_BYTES_PER_CHUNK = LOG_BYTES_IN_CHUNK - LOG_LIVE_COVERAGE;
  public static final int LIVE_BYTES_PER_CHUNK = 1 << LOG_LIVE_BYTES_PER_CHUNK; // Live bitmap
  public static final int HASH_BYTES_PER_CHUNK = LIVE_BYTES_PER_CHUNK; // Hash bitmap -- same space requirements as live bitmap
  public static final int META_DATA_BYTES_PER_CHUNK = LIVE_BYTES_PER_CHUNK + HASH_BYTES_PER_CHUNK;
  public static final Extent META_DATA_EXTENT_PER_CHUNK = Extent.fromIntSignExtend(META_DATA_BYTES_PER_CHUNK);
  protected static final int META_DATA_PAGES_PER_CHUNK = Conversions.bytesToPages(META_DATA_EXTENT_PER_CHUNK);

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

    int objectSize = VM.objectModel.getCurrentSize(object);
    int objectSizeWhenCopied = VM.objectModel.getSizeWhenCopied(object);
    int bitmapSize;

    if (objectSizeWhenCopied > objectSize) {
      updateHashBit(objectStartAddress, true, true);
      bitmapSize = getObjectSizeFromBitmap(object);
      if (VM.VERIFY_ASSERTIONS)
        VM.assertions._assert(objectSizeWhenCopied == bitmapSize);
    } else {
      updateHashBit(objectStartAddress, false, true);
      bitmapSize = getObjectSizeFromBitmap(object);
      if (VM.VERIFY_ASSERTIONS)
        VM.assertions._assert(objectSize == bitmapSize);
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

    int hashCodeBytes = hashBitSet(objectStartAddress) ? BYTES_IN_WORD : 0;
    return (count << LOG_BYTES_IN_WORD) + hashCodeBytes;
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
  private static Word getMask(Address address, boolean set) {
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
  private static Address getLiveWordAddress(Address address) {
    Address rtn = EmbeddedMetaData.getMetaDataBase(address);
    return rtn.plus(EmbeddedMetaData.getMetaDataOffset(address,
        LOG_LIVE_COVERAGE, LOG_BYTES_IN_WORD));
  }

  private static Address getObjectEndAddress(ObjectReference object) {
    int size = VM.objectModel.getCurrentSize(object);
    return VM.objectModel.objectStartRef(object).plus(size).minus(BYTES_IN_WORD);
  }

}
