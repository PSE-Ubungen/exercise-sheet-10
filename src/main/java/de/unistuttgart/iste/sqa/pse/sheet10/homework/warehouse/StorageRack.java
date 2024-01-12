package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Represents a warehouse that can hold a fixed number of items.
 * The number of holdable items is defined by the capacity of the storage rack.
 *
 * @author Levin Kohler
 */
public final class StorageRack {
	// @ private instance invariant capacity > 0;
	// @ private instance invariant numberOfItems >= 0;
	// @ private instance invariant numberOfItems <= capacity;

	private final int capacity;
	private int numberOfItems;
	List<Optional<StationeryItem>> storageRack;
	Map<Identifier, Integer> catalog;

	/*@
	@ requires capacity > 0;
	@ ensures this.capacity == capacity;
	@ ensures numberOfItems == 0;
	@ ensures (\forall int i; 0 <= i && i < capacity; storageRack.get(i).isEmpty());
	@ ensures catalog.isEmpty();
	@*/
	/**
	 * Creates a new storage rack with the given capacity.
	 *
	 * @param capacity capacity of the storage rack.
	 *
	 * @throws IllegalArgumentException If capacity is less than 1.
	 */
	public StorageRack(final int capacity) {
		if (capacity <= 0) {
			throw new IllegalArgumentException("A warehouse must have a minimum capacity of 1.");
		}
		this.capacity = capacity;
		numberOfItems = 0;
		catalog = new HashMap<>();
		storageRack = new ArrayList<>();

		//@ loop_invariant 0 <= index && index <= capacity;
		for (int index = 0; index < capacity; index++) {
			storageRack.add(index, Optional.empty());
		}
	}

	/*@
    @ requires (\exists int i; 0 <= i && i < capacity; storageRack.get(i).isEmpty());
    @ ensures (\exists int i; 0 <= i && i < capacity; storageRack.get(i).isPresent() && storageRack.get(i).get() == stationeryItem);
    @ ensures catalog.containsKey(stationeryItem.getIdentifier());
    @*/
	/**
	 * The function adds a stationery item to a storage rack at the first empty compartment and updates the catalog.
	 * 
	 * @param stationeryItem The stationery item that gets added.
	 * 
	 * @throws IllegalArgumentException If there is no empty compartment available.
	 */
	public void addItem(final StationeryItem stationeryItem) {
		int index = 0;

		//@ loop_invariant 0 <= index && index <= capacity;
        //@ loop_invariant (\forall int j; 0 <= j && j < index; storageRack.get(j).isPresent());
		while (storageRack.get(index).isEmpty() || index > capacity) {
			index++;
		}

		if (index > capacity) {
			throw new IllegalArgumentException("The storage rack is full.");
		}
		else{
			storageRack.add(index, Optional.of(stationeryItem));
			catalog.put(stationeryItem.getIdentifier(), index);
		}
	}

	/*@
    @ requires storageRack.get(compartmentNumber).isPresent();
    @ ensures storageRack.get(compartmentNumber).isEmpty();
    @ ensures !catalog.containsKey(storageRack.get(compartmentNumber).get().getIdentifier());
    @*/
	/**
	 * The removeItem function removes an item from a storage rack at a specified compartment number.
	 * 
	 * @param compartmentNumber The compartmentNumber parameter is an integer that represents the number
	 * of the compartment in the storage rack from which the item needs to be removed.
	 * 
	 * @throws IllegalArgumentException If the specified storage rack compartment is empty.
	 */
	public void removeItem(final int compartmentNumber) {
		Optional<StationeryItem> item = storageRack.get(compartmentNumber);
		
		if (item.isEmpty()) {
			throw new IllegalArgumentException("The storage rack is empty at that location.");
		}
		else {
			catalog.remove(item.get().getIdentifier());
			storageRack.remove(compartmentNumber);
		}
	}

	/*@
    @ requires 0 <= compartmentNumber && compartmentNumber < capacity;
    @ ensures \result.equals(storageRack.get(compartmentNumber));
    @*/
	/**
	 * The getItem function returns an Optional object containing a StationeryItem from a storage rack
	 * based on the given compartment number.
	 * 
	 * @param compartmentNumber The compartment number of the storage rack where the stationery item is
	 * located.
	 * @return The method is returning an Optional object that contains a StationeryItem.
	 */
	public /*@ pure @*/ Optional<StationeryItem> getItem(final int compartmentNumber) {
		return storageRack.get(compartmentNumber);
	}

	/*@
    @ ensures catalog.containsKey(identifier) == \result.isPresent();
    @*/
	/**
	 * The function returns the compartment number associated with a given identifier.
	 * 
	 * @param identifier The unique `identifier` parameter of a specific item.
	 * @return The method is returning the compartmentnumber as an Optional<Integer> object.
	 */
	public /*@ pure @*/ Optional<Integer> getCompartmentNumberOf(final Identifier identifier) {
		Integer index = catalog.get(identifier);
		Optional<Integer> compartmentNumber;
		
		if (index == null) {
			compartmentNumber = Optional.empty();
		}
		else{
			compartmentNumber = Optional.of(index);
		}
		
		return compartmentNumber;
	}

	/*@
	@ ensures \result == capacity;
	@*/
	/**
	 * @return The capacity of this warehouse in items.
	 */
	public /*@ pure @*/ int getCapacity() {
		return capacity;
	}

	/*@
	@ ensures \result == numberOfItems;
	@*/
	/**
	 * @return The number of items in this warehouse.
	 */
	public /*@ pure @*/ int getNumberOfItems() {
		return this.numberOfItems;
	}
}
