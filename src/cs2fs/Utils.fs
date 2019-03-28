module cs2fs.Utils
let memoize (f: 'a -> 'b) =
    let cache = System.Collections.Concurrent.ConcurrentDictionary<_, _>(HashIdentity.Structural)
    fun x ->
        cache.GetOrAdd(x, lazy (f x)).Force()

module Option =
    let condition f x = if f x then Some x else None
    let conditional p x = if p then Some x else None

module String =
    let isNullOrEmpty (s:string) = System.String.IsNullOrEmpty s
    let startsWith (prefix: string) (s:string) = s.StartsWith prefix
    let endsWith (postfix: string) (s:string) = s.StartsWith postfix

module Dict =
    type dict<'Key, 'Value> = System.Collections.Generic.IDictionary<'Key, 'Value>
    let tryFind k (dictionary : dict<'Key, 'T>) =
        match dictionary.TryGetValue k with
        | false, _ -> None
        | true, v -> Some v