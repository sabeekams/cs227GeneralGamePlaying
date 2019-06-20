package player.gamer.statemachine.cs227b;

import java.util.HashSet;
import java.util.Set;

public class OurMachineState{
	private Set<Integer> contents;

	public OurMachineState() {
		this.contents = new HashSet<Integer>();
	}

	public Set<Integer> getContents()
	{
		return contents;
	}

	public void add(Integer value){
		contents.add(value);
	}
	
	public boolean equals(Object o)
	{
		if ((o != null) && (o instanceof OurMachineState))
		{
			OurMachineState state = (OurMachineState) o;
			return state.getContents().equals(getContents());
		}
		return false;
	} 
}
