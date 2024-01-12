package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import java.util.LinkedList;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;

/**
 * Represents a buffer for temporary storage of stationery items.
 * This class provides functionality to add items to the buffer, release them,
 * and check if the buffer is empty.
 *
 * @author Levin Kohler
 */
public final class Buffer {

    LinkedList<StationeryItem> list;

	/*@
	@ ensures list != null;
	@*/
    /**
     * Constructs a new Buffer object. 
     * Initializes an empty LinkedList to store stationery items.
     */
    public Buffer() {
        list = new LinkedList<>();
    }
	
	/*@
	@ requires stationeryItem != null;
	@ ensures list.contains(stationeryItem);
	@*/
    /**
     * Adds a stationery item to the buffer.
     * 
     * @param stationeryItem The stationery item to be added to the buffer.
     * @throws NullPointerException if stationeryItem is null.
     */
    public void bufferItem(final StationeryItem stationeryItem) {
        list.add(stationeryItem);
    }

	/*@
	@ requires !list.isEmpty();
	@ ensures \old(list).size() - 1 == list.size();
	@ ensures \result != null;
	@*/
    /**
     * Releases and returns the first item from the buffer.
     * 
     * @return The first stationery item in the buffer.
     * @throws NoSuchElementException if the buffer is empty.
     */
    public StationeryItem releaseItem() {
        StationeryItem item = list.getFirst();
        list.removeFirst();
        return item;
    }

	/*@
	@ ensures \result == (list.size() == 0);
	@*/
    /**
     * Checks if the buffer is empty.
     * 
     * @return true if the buffer is empty, false otherwise.
     */
    public /*@ pure @*/ boolean isEmpty() {
        return list.isEmpty();
    }
}
