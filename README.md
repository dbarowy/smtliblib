# smtliblib

This library is an SMTLIBv2 parser and AST. It is useful in two scenarios:

1. You need to parse SMTLIBv2 formulae into an AST.
2. You need to programmatically construct SMTLIBv2 formulae using AST node constructors, optionally outputting them as SMTLIBv2 text.

Note that this library is not yet complete. See [Contributing](#Contributing) below.

## Getting it

This library is available in NPM.

```
$ npm i smtliblib
```

`smtliblib` depends on the [parsecco](https://github.com/williams-cs/parsecco) parser library as well as [Typescript](https://www.typescriptlang.org/).

## Using it

The easiest way to use `smtliblib` is to use the top-level parsing function in the `SMT` namespace. The following example

```
import { SMT } from "smtliblib";

const text = "(define-fun plus ((a Int) (b Int)) Int (+ a b))";
const output = SMT.parse(text);
console.out(JSON.stringify(output));
```

will produce an AST that looks something like:

```
[
   {
      "name":"plus",
      "parameterList":[
         {
            "name":"a",
            "sort":{
               "value":0
            }
         },
         {
            "name":"b",
            "sort":{
               "value":0
            }
         }
      ],
      "returnSort":{
         "value":0
      },
      "impl":{
         "terms":[
            {
               "name":"a"
            },
            {
               "name":"b"
            }
         ]
      }
   }
]
```

## Contributing

This library is currently incomplete. I add features to it as I need them.

If you need a specific feature, feel free to [open an issue](https://github.com/dbarowy/smtliblib/issues). I am also happy to accept contributions via pull request.

## Acknowledgements

Development of this library was supported while working as a Visiting Researcher at Microsoft Research.
