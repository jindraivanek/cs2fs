public class MyClass
{
    public int Prop { get; set; }
    public int PropGet { get; }
    public int Field;
    public int PropGet2 { get {return Field;} }
    public int PropGetSet { get {var x=1; return x;} set {Field = value;} }
    
    private int MyMethod(int x, string s)
    {
        var y = x+1;
        int z = y*2;
        return x+y+z;
    }
}