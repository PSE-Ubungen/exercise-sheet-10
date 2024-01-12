package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Compass;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Pen;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Ruler;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;

import java.util.HashSet;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

/**
 * Represents a company.
 *
 * A company stores items and processes orders.
 *
 * @author Levin Kohler
 */
public final class Company {

	private final StorageRack itemStorageRack;
	private final Buffer orderBuffer;
	private final Set<Customer> knownCustomers;

	/*@
    @ ensures itemStorageRack != null;
    @ ensures orderBuffer != null;
    @ ensures knownCustomers != null;
    @*/
	/**
	 * Constructs a new Company instance with an order buffer, storage rack, and a set of known customers.
	 */
	public Company() {
		orderBuffer = new Buffer();
		itemStorageRack = new StorageRack(75);
		knownCustomers = new HashSet<>();
	}

	/*@
    @ requires stationeryItem != null;
    @*/
	/**
	 * Stores a given stationery item in the storage rack.
	 * 
	 * @param stationeryItem The stationery item to be stored.
	 */
	public void storeInStorageRack(final StationeryItem stationeryItem) {
		try {
			itemStorageRack.addItem(stationeryItem);
		} catch (IllegalArgumentException e) {
			System.out.println(e.getMessage());
		}
	}

	/*@
    @ requires identifier != null;
    @ requires customer != null;
    @ ensures knownCustomers.contains(customer) ==> orderBuffer.size() == \old(orderBuffer.size()) + 1;
    @ ensures !knownCustomers.contains(\old(customer)) ==> orderBuffer.size() == \old(orderBuffer.size()) + 2;
    @*/
	/**
	 * Processes an incoming order by identifying the compartment of the item and buffering it.
	 * If the customer is new, a bonus item is also buffered.
	 * 
	 * @param identifier The identifier of the ordered item.
	 * @param customer The customer placing the order.
	 */
	public void processIncomingOrder(final Identifier identifier, final Customer customer) {
		Optional<Integer> compartmentNumber = itemStorageRack.getCompartmentNumberOf(identifier);
		
		if (!compartmentNumber.isEmpty()) {
			Optional<StationeryItem> item = itemStorageRack.getItem(compartmentNumber.get());
			orderBuffer.bufferItem(item.get());
			if (!knownCustomers.contains(customer)) {
				orderBuffer.bufferItem(getBonusItem());
				knownCustomers.add(customer);
			}
		}
	}

	/*@
	@ ensures \result != null;
	@ ensures \result.getIdentification().getType() == ItemType.PRESENT;
	@*/
	/**
	 * Generates a bonus item for marketing reasons.
	 *
	 * @return A marketing bonus item.
	 */
	private /*@ pure @*/ StationeryItem getBonusItem() {

		switch ((new Random().nextInt(3))) {
			case 1:
				return new Compass(new Identifier(), "A marketing bonus item.");
			case 2:
				return new Ruler(new Identifier(), "A marketing bonus item.");
			default:
				return new Pen(new Identifier(), "A marketing bonus item.");
		}
	}

	/**
	 * If items are waiting for packaging, takes the next available item from the buffer and return it.
	 *
	 * @return Optional next available item for packaging, or an empty Optional if there is none.
	 */
	public Optional<StationeryItem> takeItemForPackaging() {
		if (orderBuffer.isEmpty()) {
			return Optional.empty();
		} else {
			return Optional.of(orderBuffer.releaseItem());
		}
	}
}
