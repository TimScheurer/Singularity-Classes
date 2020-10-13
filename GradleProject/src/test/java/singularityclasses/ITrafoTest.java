package singularityclasses;

public interface ITrafoTest {
	
	//@ public instance ghost \locset footprint;
	
	/*@ public normal_behaviour
	  @ ensures \dl_isolated_from(footprint, \result);
	  @ assignable \strictly_nothing;
	  @ accessible footprint;
	  @*/
	public Object test();
	
	/*@ public normal_behaviour
	  @ ensures \new_elems_fresh(footprint);
	  @ assignable footprint;
	  @*/
	public void test2();
	
    /*@ public normal_behaviour
      @ requires \dl_isolated_from(footprint, other);
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public void test3(ITrafoTest other);
	
	/*@ public normal_behaviour
	  @ ensures \fresh(\result);
	  @ ensures \new_elems_fresh(\result.footprint);
	  @ assignable \nothing;
	  @*/
 	public static ITrafoTest newInstance() {
		return new TrafoTest();
	}
}