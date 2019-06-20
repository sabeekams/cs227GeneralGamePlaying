package player.gamer.statemachine.cs227b;

import java.util.HashMap;

public class Timer {

	private long start;
	private String name;
	// Value is array of 2 longs, where the first is total time and the second is total calls
	public static HashMap<String, long[]> nameToTotalTimeAndCalls = new HashMap<String, long[]>();
	
	public Timer() {
		start = System.nanoTime();
		StackTraceElement[] st = Thread.currentThread().getStackTrace();
		name = st[2].getMethodName();
	}
	
	public Timer(String nameParam) {
		start = System.nanoTime();
		name = nameParam;
	}
	
	public void stop() {
		long finish = System.nanoTime();
		if (nameToTotalTimeAndCalls.get(name) == null) {
			long[] totalTimeAndCalls = {0, 0};
			nameToTotalTimeAndCalls.put(name, totalTimeAndCalls);
		}
		long[] totalTimeAndCalls = nameToTotalTimeAndCalls.get(name);
		totalTimeAndCalls[0] = totalTimeAndCalls[0] + finish - start;
		totalTimeAndCalls[1]++;
		report();
	}
	
	public void stop(String newName) {
		name = newName;
		stop();
	}
	
	public static void report() {
		for (String method: nameToTotalTimeAndCalls.keySet()) {
			long[] totalTimeAndCalls = nameToTotalTimeAndCalls.get(method);
			double time = totalTimeAndCalls[0] / 1000000.0;
			long calls = totalTimeAndCalls[1];
			System.out.println(method + " / " + time + " / " + calls + " / " + time/calls);
		}
	}
	
	
	
}
