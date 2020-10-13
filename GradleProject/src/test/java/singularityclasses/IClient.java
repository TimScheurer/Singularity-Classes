package singularityclasses;

public interface IClient {
	
	/*@ public normal_behaviour
	  @ requires test1 != test2;
	  @ requires \invariant_for(test2);
	  @*/
	public void test(ITrafoTest test1, ITrafoTest test2);
}