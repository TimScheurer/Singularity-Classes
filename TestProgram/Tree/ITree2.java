package Tree;

public interface ITree2 {

    //@ public instance ghost \bigint footprint;
    //@ public instance model int value;
    //@ public instance model nullable ITree2 leftTree;
    //@ public instance model nullable ITree2 rightTree;

    //@ public accessible \inv : footprint;
    //@ public accessible value : footprint;
    //@ public accessible leftTree : footprint;
    //@ public accessible rightTree : footprint;

    /*@ public normal_behaviour
      @ requires isUniform(value);
      @ ensures value == \old(value) + 1;
      @ ensures isUniform(value);
      @ assignable footprint;
      @*/
    public void increment();

    /*@
      @ ensures \result == value;
      @ ensures_free \result == getVal();
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
      @ ensures \fresh(\result);
      @ ensures \result != null;
      @ assignable \nothing;
      @*/
    public static ITree2 newInstance(int val) {
        return new Tree2(val);
    }
}