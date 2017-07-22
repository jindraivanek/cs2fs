public class MyClass<T>
{
    private bool MyMethod<U>(T x, U y)
    {
        return x == y;
    }
}