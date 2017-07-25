using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ConsoleApplication3
{
    class Example
    {
        public string Conditionals()
        {
            var x = 1 > 2 ? "a" : "b";
            return x;
        }

        public string Arrays(string[] strings)
        {
            if (strings == null)
            {
                return "null";
            } 
            else 
            {
                var x = "";
                foreach (var s in strings)
                {
                    x += "," + s;
                }
                return x;
            }
        }

        public List<int> Linq()
        {
            int[] ints = {1, 2, 3, 4, 5, 6, 7, 8};
            var big = ints.Where(i => i > 4).Select(i => i*2).ToList();
            return big;
        }

        public string Delegates()
        {
            Action<int, string> del = (a, b) =>
            {
                Console.WriteLine("{0} {1}", a, b);
            };
            Func<int, string> del2 = a => "hello" + a;
            InvokeIt(del);
            return del2(1);
        }

        private void InvokeIt(Action<int, string> del)
        {
            del(1, "hello");
        }

        public static void Main()
        {
            var i = 1.ToString();
            Console.WriteLine(i);
            var x = new Example();
            Console.WriteLine(x.Conditionals());
            Console.WriteLine(x.Arrays(null));
            string[] strings = {"F","O","O"};
            Console.WriteLine(x.Arrays(strings));
            x.Linq().ForEach(y => Console.WriteLine(y));
            Console.WriteLine(x.Delegates());
        }
    }
}