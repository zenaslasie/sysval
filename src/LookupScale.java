/** This class encapsulates lookup table scales. */

class LookupScale {
	
	/** Stores the scale (so called) break points.
	  * Scales are required to be strictly monotone,
	  * with raising values. */
	int[] values;

	// INVARIANT(S)
	//@ invariant (\forall int i; i >=0 && i < values.length - 2; values[i+1] - values[i] > 0 && values[i+2] - values[i+1] == values[i+1] - values[i]);
	//each pair must have a delta of larger than 0 and be equal to the delta of the next pair
	
	/**
	 * Construct the scale with predefined break points
	 * @param values the array with break point values
	 */
	// CONTRACT 
	//@ ensures (\forall int i; i >=0 && i < values.length; this.values[i]==values[i]);
	LookupScale(int[] values) {
		this.values = values;
	}
	
	/**
	 * Construct a linear scale that has size break points equally
	 * distributed between min and max values. 
	 * @param min minimal value of the scale
	 * @param max maximal value of the scale
	 * @param size number of break points in the scale
	 */
	// CONTRACT
	//@ requires min >=0 && max > min && size > 0;
	//@ requires (\forall int i; i >=0 && i < size; this.values[i]==0);
	//@ ensures this.values[0]==min;
	//@ ensures (\forall int i; i >=1 && i < this.values.length; this.values[i]== this.values[i-1] + (max - min)/(size -1));
	
	LookupScale(int min, int max, int size) {
		this.values = new int[size];
		//that values[0] may be a null dereference and checking division by zero 
		//@ assume values != null && values.length == size && size != 1;
		int chunk = (max - min) / (size - 1);
		this.values[0] = min;
		for(int i=1; i<this.values.length; i++) {
		  this.values[i] = this.values[i-1] + chunk;
		};
	}

	/**
	 * Looks up a sensor value in the scale and returns the scale index
	 * corresponding to the position of the sensor value in the scale. 
	 * @param sv the sensor value that should be looked up the scale
	 * @return the scale index (integral and fractional part)
	 */
	// CONTRACT
	//@ invariant (\forall int i; i >=0 && i < values.length - 2; values[i+1] - values[i] > 0 && values[i+2] - values[i+1] == values[i+1] - values[i]);
		ScaleIndex lookupValue(SensorValue sv) {
		int v = sv.getValue();
		// First get the integral part
		// The most convenient way to lookup scales is from the end
		int intPart = this.values.length - 1;
		while(intPart >= 0) {
			if(v >= this.values[intPart]) {
				break;
			}
			intPart--;
		}
		// ASSERTION
		//@ assert v >= this.values[intPart];
		//@ assert intPart >= 0;
		//@ assert intPart <= this.values.length - 1;
		int fracPart = 0;
		// Check border cases
		if(intPart == this.values.length - 1 || v < this.values[0]) {
			// ASSERTION(S)
			//@ assert v < this.values[0] || v > this.values[this.values.length];
			return new ScaleIndex(intPart, fracPart, this.values.length);
		}
		// Then calculate the fractional part
		fracPart = (v - this.values[intPart]) * 100 / (this.values[intPart+1] - this.values[intPart]);
		// ASSERTION(S)
		//@assert fracPart >= 0 && fracPart < this.values[intPart+1] - this.values[intPart];
		return new ScaleIndex(intPart, fracPart, this.values.length);
	}

	/**
	 * Provide a human readable version of this object, makes 
	 * the output of JMLUnitNG more readable.
	 */
	//@ skipesc;
	public String toString() {
		String r = "Scale of size "+this.values.length+": [";
		for(int i = 0; i<this.values.length; i++) {
			r += ""+(i==0 ? "" : ", ")+values[i];
		}
		r += "]";
		return r;
	}

}
