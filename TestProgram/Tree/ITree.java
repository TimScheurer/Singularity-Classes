package Tree;

public interface ITree {

    //@ public instance ghost \locset footprint;
    //@ public instance model int value;
    //@ public instance model nullable ITree leftTree;
    //@ public instance model nullable ITree rightTree;

    //@ public instance invariant \subset(\singleton(footprint), footprint);

    //@ public accessible \inv : footprint;
    //@ public accessible value : footprint;
    //@ public accessible leftTree : footprint;
    //@ public accessible rightTree : footprint;

    /*@ public normal_behaviour
      @ requires isUniform(value);
      @ ensures \new_elems_fresh(footprint);
      @ ensures value == \old(value) + 1;
      @ ensures isUniform(value);
      @ assignable footprint;
      @*/
    public void increment();

    /*@
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public int getVal();

    /*@ public normal_behaviour
      @ ensures \result ==> value == val;
      @ ensures \result <==> (value == val) &&
      @                    (leftTree == null || leftTree.isUniform(val)) &&
      @                    (rightTree == null || rightTree.isUniform(val));
      @ ensures_free \result == isUniform(val);
      @ assignable \strictly_nothing;
      @ accessible footprint;
      @*/
    public boolean isUniform(int val);

    /*@ public normal_behaviour
      @ ensures \new_elems_fresh(\result.footprint);
      @ ensures \fresh(\result);
      @ ensures \result != null;
      @ assignable \nothing;
      @*/
    public static ITree newInstance(int val) {
        return new Tree(val);
    }
}