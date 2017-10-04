/**
 * An encapsulation class that stores the scale index, that is,
 * its integral and fractional (0..99%) part. It also stores the size
 * of the lookup scale that this index refers to. 
 */
class ScaleIndex {

	/** Integral part. */
	int intPart;
	
	/** Fractional part. */
	int fracPart;
	
	/** The size of the corresponding scale this index refers to. */
	int size;      

	// INVARIANT(S)
	//@ invariant fracPart >= 0 && fracPart <= 99;
	
	// MODEL

	/**
	 * Constructs a new index with the given parameters.
	 * @param intPart integral part
	 * @param fracPart fractional (0..99) part
	 * @param size the size of the underlying scale
	 */
	// CONTRACT
	//@ensures this.intPart == intPart;
	//@ensures this.fracPart == fracPart;
	//@ensures this.size == size;
	ScaleIndex(int intPart, int fracPart, int size) {
		this.intPart = intPart;
		this.fracPart = fracPart;
		this.size = size;
	}
	
	/**
	 * @return the integral part
	 */
	// CONTRACT
	//@ensures \result == intPart;
	/*@ pure @*/
	int getIntPart() {
		return intPart;
	}

	/**
	 * @return the fractional part
	 */
	// CONTRACT
	//@ensures \result == fracPart;
	/*@ pure @*/
	int getFracPart() {
		return fracPart;
	}

	/**
	 * @return the size of the underlying scale
	 */
	// CONTRACT
	//@ensures \result == size;
	/*@ pure @*/
	int getSize() {
		return size;
	}

}
