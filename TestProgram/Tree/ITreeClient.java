package Tree;

public interface ITreeClient {

    /*@ public normal_behaviour
      @ requires tree1 != tree2;
      @ requires \invariant_for(tree1);
      @ requires tree1.isUniform(0);
      @ ensures tree1.isUniform(1);
      @ ensures tree2.getVal() == \old(tree2.getVal());
      @*/
    public void test(ITree tree1, ITree tree2);
}