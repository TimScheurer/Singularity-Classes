package singularityclasses;

public class TrafoTest implements ITrafoTest {

	private ITrafoTest test;

    public TrafoTest() {
        //@ set footprint = \set_union(\all_fields(this), test.footprint);
    }

    public Object test(Object param) {
        
        //@ assert \dl_valid_receiver(footprint, test);
        test.test3(this);
        
        return test;
    }

    public void test2() {
        int i = 42;
    }
    
    public void test3(ITrafoTest other) {
        other.test2();
    }
}