using System;

public class B {
    int x;
}

public class Amb : B, IDisposable
{
    public void Dispose()
    {
    }
}
