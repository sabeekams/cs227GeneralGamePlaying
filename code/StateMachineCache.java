package player.gamer.statemachine.cs227b;

import java.util.HashMap;

public class StateMachineCache<K, V> {
	private HashMap<K, V> primaryCache;
	private HashMap<K, V> secondaryCache;
	
	public StateMachineCache() {
		primaryCache = new HashMap<K, V>();
		secondaryCache = new HashMap<K, V>();
	}

	public V retrieve(K key) {
		V value = primaryCache.get(key);
		if (value != null)
			secondaryCache.put(key, value);
		return value;
	}
	
	public V retrieveNoCache(K key) {
		return primaryCache.get(key);
	}
	
	public void cache(K key, V value) {
		double freeMemoryRatio = SystemCalls.getFreeMemoryRatio();
		if (freeMemoryRatio > SystemCalls.stopFillingPrimaryCacheThreshold) {
			primaryCache.put(key, value);
		} else if (freeMemoryRatio > SystemCalls.stopFillingSecondaryCacheThreshold) {
			secondaryCache.put(key, value);
		}
	}
	
	public void swapCaches() {
		primaryCache = secondaryCache;
		secondaryCache = new HashMap<K, V>();
	}
	
	public void report(){
		System.out.println("Primary: " + primaryCache.size() + " Secondary: " + secondaryCache.size());
	}
	
}
