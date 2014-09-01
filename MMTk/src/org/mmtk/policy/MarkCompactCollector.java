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

import org.mmtk.plan.markcompact.MC;
import org.mmtk.utility.Constants;
import org.mmtk.utility.Log;
import org.mmtk.utility.alloc.Allocator;
import org.mmtk.utility.alloc.BumpPointer;
import org.mmtk.utility.alloc.EmbeddedMetaData;
import org.mmtk.vm.VM;
import org.vmmagic.pragma.Inline;
import org.vmmagic.pragma.Uninterruptible;
import org.vmmagic.unboxed.Address;
import org.vmmagic.unboxed.Extent;
import org.vmmagic.unboxed.ObjectReference;
import org.vmmagic.unboxed.Word;

/**
 * This class implements unsynchronized (local) per-collector-thread elements of a
 * sliding mark-compact collector.<p>
 *<p>
 * Specifically, this class provides the methods that
 * <ul>
 *  <li>Calculate the forwarding pointers for heap objects, in a linear pass over
 *   (part of) the heap</li>
 *  <li>Performs the compaction pass over the heap.</li>
 * </ul>
 *<p>
 * Each collector thread maintains a private list of the pages that it compacts.
 * If it runs out of work during the calculateForwardingPointers pass, it requests
 * a new region from the global MarkCompactSpace.  Regions compacted by a collector
 * remain local to the collector.
 *
 * @see MarkCompactSpace
 * @see MarkCompactLocal
 */
@Uninterruptible
public final class MarkCompactCollector {

  private static final int HASH_OFFSET = MarkCompactSpace.LIVE_BYTES_PER_CHUNK;
  private static final int ALIGNMENT_OFFSET = HASH_OFFSET + MarkCompactSpace.HASH_BYTES_PER_CHUNK;

  static final boolean VERBOSE = false;

  static final boolean TMP_VERBOSE = false;

  static final boolean VERY_VERBOSE = VERBOSE && false;

  private final MarkCompactSpace space;

  /**
   * This collector's work list
   */
  private Address regions = Address.zero();

  private final FromCursor fromCursor = new FromCursor();
  private final ToCursor toCursor = new ToCursor();

  /**
   * Constructor
   *
   * @param space The space to bump point into.
   */
  public MarkCompactCollector(MarkCompactSpace space) {
    this.space = space;
  }

  /* ********************************************************************************
   *
   *                Cursor classes
   *
   */

  /**
   * Both the 'compact' and 'calculate' phases can be thought of as sweeping
   * a pair of cursors across a linked list of regions.  Each cursor requires
   * maintaining pointers to the current region, the current address and the end of
   * the region.  The regionCursor class maintains these 3 pointers, while the
   * subclasses ToCursor and FromCursor provide methods specific to the
   * read and write pointers.
   */
  @Uninterruptible
  private abstract static class RegionCursor {

    /** Name of the cursor - for debugging messages */
    private final String name;

    /**
     * The current region, or zero if the cursor is invalid (eg after advancing
     * past the end of the current work list
     */
    protected Address region;

    /**
     * The limit of the current region. When reading a populated region, this is the
     * address of the last used byte.  When writing to a fresh region, this is the last
     * byte in the region.
     */
    protected Address limit;

    /** The current address */
    protected Address cursor;

    /**
     * @param name The name of the region - for debugging messages.
     */
    public RegionCursor(String name) {
      this.name = name;
    }

    /**
     * Hook to allow subclasses to initialize the cursor in different ways.
     *
     * @param region The region to be processed.
     */
    abstract void init(Address region);

    /**
     * Assert that the cursor is within the bounds of the region.  Calls to this
     * must be guarded by {@code if (VM.VERIFY_ASSERTIONS)}
     */
    protected void assertCursorInBounds() {
      VM.assertions._assert(!region.isZero());
      VM.assertions._assert(cursor.GE(BumpPointer.getDataStart(region)),
      "Cursor is below start of region");
      VM.assertions._assert(cursor.LE(limit),"Cursor beyond end of region");
    }

    /**
     * Increment the cursor.
     * @param size Bytes to increment by
     */
    void inc(int size) {
      this.cursor = cursor.plus(size);
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
    }

    /**
     * Increment the cursor to a specific address
     * @param cursor Destination address
     */
    public void incTo(Address cursor) {
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
      if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(cursor.GE(this.cursor));
      this.cursor = cursor;
    }

    /**
     * @param other Other region
     * @return {@code true} if this cursor points to the same region as {@code other}
     */
    boolean sameRegion(RegionCursor other) {
      return region.EQ(other.getRegion());
    }

    /**
     * @param size Size in bytes
     * @return {@code true} if {@code size} bytes are available in the current region
     */
    boolean isAvailable(int size) {
      return cursor.plus(size).LE(limit);
    }

    /**
     * @return The current cursor
     */
    public Address get() {
      return cursor;
    }

    /**
     * @return The current region pointer
     */
    public Address getRegion() {
      return region;
    }

    /**
     * @return The current region limit
     */
    public Address getLimit() {
      return limit;
    }

    /**
     * Follow the linked-list of regions to the next region.
     */
    void advanceToNextRegion() {
      Address nextRegion = MarkCompactLocal.getNextRegion(region);
      if (nextRegion.isZero()) {
        region = Address.zero();
      } else {
        init(nextRegion);
        if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
      }
    }

    void advanceToNextChunk(MarkCompactSpace space) {
      Address oldChunkBase = EmbeddedMetaData.getMetaDataBase(cursor);
      while (EmbeddedMetaData.getMetaDataBase(cursor).EQ(oldChunkBase)) {
        Address nextRegion = BumpPointer.getNextRegion(region);
        if (nextRegion.isZero()) {
          nextRegion = space.getNextRegion();
          if (nextRegion.isZero()) {
            region = Address.zero();
            return;
          }
          MarkCompactLocal.setNextRegion(region,nextRegion);
          MarkCompactLocal.clearNextRegion(nextRegion);
        }
        init(nextRegion);
      }
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
    }

    /**
     * Advance the cursor either to the next region in the list,
     * or to a new region allocated from the global list.
     * @param space
     */
    void advanceToNextForwardableRegion(MarkCompactSpace space) {
      Address nextRegion = BumpPointer.getNextRegion(region);
      if (nextRegion.isZero()) {
        nextRegion = space.getNextRegion();
        if (nextRegion.isZero()) {
          region = Address.zero();
          return;
        }
        MarkCompactLocal.setNextRegion(region,nextRegion);
        MarkCompactLocal.clearNextRegion(nextRegion);
      }
      init(nextRegion);
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
    }

    /**
     * @return {@code true} if we haven't advanced beyond the end of the region list
     */
    boolean isValid() {
      return !region.isZero();
    }

    /**
     * @param ref The object in question
     * @return {@code true} if the object's start address is in this region
     */
    @Inline
    boolean isInRegion(ObjectReference ref) {
      Address addr = VM.objectModel.refToAddress(ref);
      return addr.GE(BumpPointer.getDataStart(region)) && addr.LE(limit);
    }

    /**
     * Print the cursor - for debugging
     */
    void print() {
      Log.write(name); Log.write(" cursor:");
      Log.write(" region="); Log.write(region);
      Log.write(" limit="); Log.write(limit);
      Log.write(" cursor="); Log.write(cursor);
      Log.writeln();

    }
  }

  /**
   * Subclass for the read-only cursor that leads the scan of regions.
   */
  @Uninterruptible
  private static final class FromCursor extends RegionCursor {
    public FromCursor() {
      super("from");
    }

    /**
     * Initialize the cursor - the limit is the end of the allocated data
     */
    @Override
    void init(Address region) {
      if (VM.VERIFY_ASSERTIONS) BumpPointer.checkRegionMetadata(region);
      this.region = region;
      this.cursor = MarkCompactLocal.getDataStart(region);
      this.limit = MarkCompactLocal.getDataEnd(region);
    }

    /**
     * Advance from the cursor to the start of the next object.
     * @return The object reference of the next object.
     */
    @Inline
    ObjectReference advanceToObject() {
      ObjectReference current = VM.objectModel.getObjectFromStartAddress(cursor);
      cursor = VM.objectModel.objectStartRef(current);
      if (VM.VERIFY_ASSERTIONS) {
        Address lowBound = BumpPointer.getDataStart(region);
        VM.assertions._assert(cursor.GE(lowBound) && cursor.LE(limit),"Cursor outside region");
      }
      return current;
    }

    /**
     * Advance the cursor to the end of the given object.
     */
    @Inline
    void advanceToObjectEnd(ObjectReference current) {
      cursor = VM.objectModel.getObjectEndAddress(current);
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
    }

    /**
     * Override the superclass with an additional assertion - we only advance
     * when we have read to the end, and the cursor must point *precisely*
     * to the last allocated byte in the region.
     */
    @Override
    void advanceToNextRegion() {
      if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(get().EQ(getLimit()));
      super.advanceToNextRegion();
    }

    /**
     * Advance the cursor either to the next region in the list,
     * or to a new region allocated from the global list.
     * @param space
     */
    @Override
    void advanceToNextForwardableRegion(MarkCompactSpace space) {
      if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(get().EQ(getLimit()));
      super.advanceToNextForwardableRegion(space);
    }

    /**
     * @return {@code true} if there are more objects in this region
     */
    boolean hasMoreObjects() {
      return cursor.LT(limit);
    }
  }

  /**
   * Subclass for the read-only cursor that follows the 'from' cursor,
   * writing or calculating the position of copied objects
   */
  @Uninterruptible
  private static final class ToCursor extends RegionCursor {
    public ToCursor() {
      super("to");
    }

    /**
     * Initialize the cursor to a given region.  The limit is the limit of
     * available space in the region.
     */
    @Override
    void init(Address region) {
      if (VM.VERIFY_ASSERTIONS) BumpPointer.checkRegionMetadata(region);
      this.region = region;
      this.cursor = MarkCompactLocal.getDataStart(region);
      this.limit = MarkCompactLocal.getRegionLimit(region);
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
    }

    /**
     * Update the metadata of the current region with the current value
     * of the cursor.  Zero the region from here to the end.
     */
    void finish() {
      if (VM.VERIFY_ASSERTIONS) assertCursorInBounds();
      Extent zeroBytes = limit.diff(cursor).toWord().toExtent();
      VM.memory.zero(false, cursor, zeroBytes);
      MarkCompactLocal.setDataEnd(region, cursor);
      MarkCompactLocal.checkRegionMetadata(region);
    }

    /**
     * Terminate the list of regions here.
     * @return The address of the (old) next region in the list.
     */
    Address snip() {
      Address nextRegion = BumpPointer.getNextRegion(region);
      BumpPointer.clearNextRegion(region);
      finish();
      return nextRegion;
    }

    /**
     * Copy an object to an address within this cursor's region.
     * @param from The source object
     * @param to The target object
     */
    @Inline
    void copy(ObjectReference from, ObjectReference to) {
      if (VM.VERIFY_ASSERTIONS) {
        VM.assertions._assert(MarkCompactSpace.getForwardingPointer(from).toAddress().EQ(to.toAddress()));
        VM.assertions._assert(cursor.GT(region) && cursor.LE(limit));
      }
      Address savedCursor = Address.zero();
      if (VM.VERIFY_ASSERTIONS) savedCursor = cursor;
      cursor = VM.objectModel.copyTo(from, to, cursor);
      if (VM.VERIFY_ASSERTIONS) {
        if (cursor.LT(BumpPointer.getDataStart(region)) || cursor.GT(limit)) {
          Log.write("Copy of "); Log.write(from);
          Log.write(" to "); Log.write(to);
          Log.write(" puts cursor at "); Log.write(cursor);
          Log.write(" (was: "); Log.write(savedCursor);
          Log.writeln(")");
        }
        VM.assertions._assert(cursor.GT(region) && cursor.LE(limit));
      }
      MarkCompactSpace.setForwardingPointer(to, ObjectReference.nullReference());
      if (VM.VERIFY_ASSERTIONS)
        VM.assertions._assert(VM.objectModel.getObjectEndAddress(to).LE(limit));
    }

    /**
     * Move to the next region, updating the metadata with the current 'write' state.
     */
    void finishAndAdvanceToNextRegion() {
      finish();
      advanceToNextRegion();
    }

    /**
     * Move to the next region, in read-only mode.  Add the assertion of validity,
     * since we shouldn't be able to fall off the end of the list while writing.
     */
    @Override
    void advanceToNextRegion() {
      super.advanceToNextRegion();
      if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(isValid());
    }
  }

  /* ***************************************************************************************** */

  /**
   * Perform a linear scan through the objects allocated by this bump pointer,
   * calculating where each live object will be post collection.<p>
   *
   * We maintain two cursors, {@code fromCursor} and {@code toCursor}, and simulate
   * copying live objects from the former to the latter.  Initially, the cursors
   * point to the first region in this collector's local list, and increment in
   * lockstep until the first dead object is encountered.  After that, the to cursor
   * trails the from cursor.<p>
   *
   * The outer loop advances the 'from' pointer
   */
  public void calculateForwardingPointers() {
    if (regions.isZero()) {
      regions = space.getNextRegion();
    }

    if (regions.isZero())
      return;

    fromCursor.init(regions);
    toCursor.init(regions);

    if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(true);

    /* Loop through active regions or until the last region */
    while (fromCursor.isValid()) {
      if (VERBOSE) {
        fromCursor.print();
        toCursor.print();
      }

      /* Loop through the objects in the current 'from' region */
      while (fromCursor.hasMoreObjects()) {
        ObjectReference current = fromCursor.advanceToObject();
        Address objectStartAddress = VM.objectModel.objectStartRef(current);
        fromCursor.advanceToObjectEnd(current);

        if (MarkCompactSpace.toBeCompacted(current)) {
          if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(MarkCompactSpace.getForwardingPointer(current).isNull());

          // Fake - allocate it.
          int size = MarkCompactSpace.getObjectSizeFromBitmap(current);
          int align = MarkCompactSpace.getObjectAlignmentFromBitmap(current);
          int offset = MarkCompactSpace.getObjectOffsetFromBitmap(current);

          // Move to the (aligned) start of the next object
          toCursor.incTo(Allocator.alignAllocationNoFill(toCursor.get(), align, offset));

          boolean objHashed = MarkCompactSpace.hashBitSet(current);
          int reservedSize = size;
          if (objHashed)
            reservedSize += Constants.BYTES_IN_WORD;

          /*
           * If we're allocating into separate regions, and we've allocated beyond the end of the
           * current region, advance to the next one.  We always allocate into regions we have
           * scanned in this collector.
           */
          if (!toCursor.sameRegion(fromCursor) && !toCursor.isAvailable(reservedSize)) {
            // The 'to' pointer always trails the 'from' pointer, guaranteeing that
            // there's a next region to advance to.
            toCursor.advanceToNextRegion();
            toCursor.incTo(Allocator.alignAllocationNoFill(toCursor.get(), align, offset));
          }

          // Get new address using compressor, and compare with ordinary MC-calculated address
          // Assert that they're equal before proceeding
          Address forwardAddress = MarkCompactSpace.getNewAddress(current, true);
          if (!toCursor.get().EQ(forwardAddress)) {
            Log.writeln();
            Log.writeln("**************************************************************************");
            MarkCompactSpace.getNewAddress(current, true);
            Address objAdr = VM.objectModel.objectStartRef(current);
            Address fromBlockStartAddress = MarkCompactSpace.getBlockAddress(objAdr);
            Address metaDataBase = EmbeddedMetaData.getMetaDataBase(objAdr);
            int blockNumber = MarkCompactSpace.getBlockNumber(objAdr);
            Address toBlockBaseAddress = MarkCompactSpace.getOffsetTableFwdAddr(blockNumber, fromBlockStartAddress, metaDataBase);

            Log.write("Compressor Fwd Addr: "); Log.write(forwardAddress);
            Log.write(". Ordinary MC Fwd Addr: "); Log.writeln(toCursor.get());
            Log.write("Object: "); Log.write(objAdr);
            Log.write(". Size: "); Log.write(reservedSize);
            Log.write(". Align: "); Log.write(align);
            Log.write(". Offset: "); Log.writeln(offset);
            Log.write("Block: "); Log.write(blockNumber);
            Log.write(". Block (offset) Addr: "); Log.writeln(toBlockBaseAddress);
            Log.writeln("**************************************************************************");
          }
          if (VM.VERIFY_ASSERTIONS)
            VM.assertions._assert(forwardAddress.EQ(toCursor.get()));

          ObjectReference target = VM.objectModel.getReferenceWhenCopiedTo(current, toCursor.get());
          if (toCursor.sameRegion(fromCursor) && target.toAddress().GE(current.toAddress())) {
            // Don't move the object.
            MarkCompactSpace.setForwardingPointer(current, current);
            toCursor.incTo(objectStartAddress.plus(size));
          } else {
            MarkCompactSpace.setForwardingPointer(current, target);
            toCursor.inc(reservedSize);
          }
        }
      }
      fromCursor.advanceToNextForwardableRegion(space);
    }
  }

  /**
   * Creates offset table from the markbit vector
   */
  public void createOffsetTable() {
    if (regions.isZero()) {
      regions = space.getNextRegion();
    }

    if (regions.isZero())
      return;

    fromCursor.init(regions);
    toCursor.init(regions);
    Address lowWaterMark = fromCursor.get();

    while (fromCursor.isValid()) {
      Log.writeln("--------------------------------------------------------------------------");
      fromCursor.print();
      toCursor.print();
      // Ensure that we never move backward to a region already seen
      if (fromCursor.get().LT(lowWaterMark)) {
        if (VM.VERIFY_ASSERTIONS) {
          // Fail if difference between low water mark and current address is more than 4MB
          int difference = lowWaterMark.diff(fromCursor.get()).toInt();
          VM.assertions._assert(difference <= (1 << 22));
        }
        Log.writeln("Below low water mark! Advancing to next chunk again...");
        fromCursor.advanceToNextChunk(space);
        continue;
      }
      // Reset low water mark to newly advanced cursor
      lowWaterMark = fromCursor.get();

      Address livemapStart = MarkCompactSpace.getLiveWordAddress(fromCursor.get());
      Address metadataStart = EmbeddedMetaData.getMetaDataBase(fromCursor.get());
      Address livemapEnd = metadataStart.plus(MarkCompactSpace.LIVE_BYTES_PER_CHUNK);
      Address currentAddress = livemapStart;
      Word mask = Word.one();

      int wordCounter = 0;
      int block = 0;
      int bitCounter = 0;
      int offset = 0;
      int align = Constants.BYTES_IN_WORD;

      boolean isLive = false;
      boolean isHashed = false;
      boolean isDoubleAligned = false;

      // startMarker denotes whether we're looking at object start/end mark bit
      // it is initially set to true, so it is satisfied upon seeing first start bit
      boolean startMarker = true;

      // flag is set to true between the time we encounter the start marker and when
      // we encounter end marker.
      boolean middleOfObject = false;
      boolean writeToOffsetTableWaiting = false;

      MarkCompactSpace.storeOffsetTableFwdAddr(block, toCursor.get(), metadataStart, false);

      while (currentAddress.LE(livemapEnd)) {
        Word value = currentAddress.loadWord();
        isLive = value.and(mask).EQ(mask);

        if (isLive) {
          if (startMarker) {
            // Start of object.
            // First Reset bit counter
            bitCounter = 1;
            middleOfObject = true;

            // Check hash bit because offset corresponds only to start marker
            Word hashValue = currentAddress.plus(HASH_OFFSET).loadWord();
            isHashed = hashValue.and(mask).EQ(mask);

            // Same as above
            Word alignValue = currentAddress.plus(ALIGNMENT_OFFSET).loadWord();
            isDoubleAligned = alignValue.and(mask).EQ(mask);
            align = (isDoubleAligned ? 2 : 1) * Constants.BYTES_IN_WORD;

            if (TMP_VERBOSE) {
              Log.write("Block: "); Log.write(block);
              Log.write(". Live Word address: "); Log.write(currentAddress);
            }
          } else {
            // End of object.
            // First get offset requirement
            Word offsetStatus = currentAddress.plus(HASH_OFFSET).loadWord();
            if (offsetStatus.and(mask).EQ(mask)) {
              Word offsetType = currentAddress.plus(ALIGNMENT_OFFSET).loadWord();
              boolean isArray = offsetType.and(mask).EQ(mask);
              offset = isArray ? MarkCompactSpace.ARRAY_HEADER_BYTES : MarkCompactSpace.SCALAR_HEADER_BYTES;
            } else {
              offset = 0;
            }

            // Align cursor appropriately
            toCursor.incTo(Allocator.alignAllocationNoFill(toCursor.get(), align, offset));

            // Add single word to object size if it has been hashed
            // We assume it is always going to move. This is simpler, and also because we
            // cannot easily calculate its original location to determine whether moving
            // is necessary. Therefore it's much simpler to just always "move" it.
            int size = bitCounter << Constants.LOG_BYTES_IN_WORD;
            size += (isHashed) ? Constants.BYTES_IN_WORD : 0;

            if (!toCursor.isAvailable(size)) {
              // The 'to' pointer always trails the 'from' pointer, guaranteeing that
              // there's a next region to advance to.
              toCursor.advanceToNextForwardableRegion(space);
              toCursor.incTo(Allocator.alignAllocationNoFill(toCursor.get(), align, offset));
            }

            if (TMP_VERBOSE) {
              Log.write(". Forward address: "); Log.write(toCursor.get());
              Log.write(". Size: "); Log.write(size);
              Log.write(". Align: "); Log.writeln(align);
            }

            // Increment destination pointer by size of object
            toCursor.inc(size);
            middleOfObject = false;
          }
          startMarker = !startMarker;
        }

        mask = mask.lsh(1);
        if (mask.EQ(Word.zero())) {
          wordCounter++;
          mask = Word.one();
          currentAddress = currentAddress.plus(Constants.BYTES_IN_WORD);
          if (wordCounter % MarkCompactSpace.WORDS_PER_BITMAP_BLOCK == 0) {
            // Crossed block boundary
            block++;
            writeToOffsetTableWaiting = true;
          }
        }

        if (!middleOfObject && writeToOffsetTableWaiting) {
          MarkCompactSpace.storeOffsetTableFwdAddr(block, toCursor.get(), metadataStart, false);
          writeToOffsetTableWaiting = false;
        }

        bitCounter++;
      }
      fromCursor.advanceToNextChunk(space);
    }
  }

  /**
   * Perform the compacting phase of the collection.
   */
  public void compact() {
    if (regions.isZero()) return;

    toCursor.init(regions);
    fromCursor.init(regions);

    /* Loop through active regions or until the last region */
    while (fromCursor.isValid()) {
      if (VERBOSE) {
        Log.write("Compacting from region "); Log.write(fromCursor.getRegion());
        Log.write(" to region "); Log.writeln(toCursor.getRegion());
      }

      /* Loop through the objects in the region */
      while (fromCursor.hasMoreObjects()) {
        ObjectReference current = fromCursor.advanceToObject();
        fromCursor.advanceToObjectEnd(current);

        ObjectReference copyTo = MarkCompactSpace.getForwardingPointer(current);
        if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(!copyTo.toAddress().EQ(Address.fromIntZeroExtend(VM.ALIGNMENT_VALUE)));

        if (!copyTo.isNull() && Space.isInSpace(MC.MARK_COMPACT, copyTo)) {
          if (VM.VERIFY_ASSERTIONS) {
            if (MarkCompactSpace.isMarked(current)) {
              Log.write("Object "); Log.write(current);
              Log.writeln(" is marked during the compact phase");
              VM.objectModel.dumpObject(current);
            }
            VM.assertions._assert(!MarkCompactSpace.isMarked(current));
          }
          if (!toCursor.isInRegion(copyTo)) {
            // Update metadata and move on
            toCursor.finishAndAdvanceToNextRegion();
          }
          if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(toCursor.isInRegion(copyTo));
          toCursor.copy(current, copyTo);
          if (VM.VERIFY_ASSERTIONS) VM.assertions._assert(toCursor.isInRegion(copyTo));
          MarkCompactSpace.setForwardingPointer(copyTo, ObjectReference.nullReference());
        }
      }
      fromCursor.advanceToNextRegion();
    }

    /* Fix up the last object pointer etc */
    toCursor.finish();


    /*
     * Return unused pages to the global page resource
     */
    Address region = toCursor.snip();
    while (!region.isZero()) {
      Address nextRegion = MarkCompactLocal.getNextRegion(region);
      space.release(region);
      region = nextRegion;
    }
  }
}
