using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.MSBuild;

namespace RoslynSymbolsTest
{
    public class InterfaceMemberImplementationTest
    {
        class MyDisposable : IDisposable
        {
            public void Dispose() { }
        }

        public void Run()
        {
            string solutionPath = @"..\..\..\RoslynSymbolsTest.sln";
            MSBuildWorkspace workspace = MSBuildWorkspace.Create();
            Solution solution = workspace.OpenSolutionAsync(solutionPath).Result;
            var project = solution.Projects.Where(p => p.Name == "RoslynSymbolsTest").Single();
            var document = project.Documents.Where(d => d.Name == "InterfaceMemberImplementationTest.cs").Single();
            var semanticModel = document.GetSemanticModelAsync().Result;

            IMethodSymbol idictionaryAddMethodSymbol = ResolveMethod(semanticModel, typeof(IDictionary<,>), "Add");
            IMethodSymbol idictionaryAddStringObjectMethodSymbol = ResolveMethod(semanticModel, typeof(IDictionary<,>), new Type[] { typeof(string), typeof(object) }, "Add");
            IMethodSymbol idictionaryAddStringStringMethodSymbol = ResolveMethod(semanticModel, typeof(IDictionary<,>), new Type[] { typeof(string), typeof(string) }, "Add");
            IMethodSymbol idictionaryGetItemMethodSymbol = ResolveMethod(semanticModel, typeof(IDictionary<,>), "get_Item");
            IMethodSymbol dictionaryMethodSymbol = ResolveMethod(semanticModel, typeof(Dictionary<,>), "Add");
            IMethodSymbol dictionaryStringObjectMethodSymbol = ResolveMethod(semanticModel, typeof(Dictionary<,>), new Type[] { typeof(string), typeof(object) }, "Add");

            IMethodSymbol idisposableDisposeMethodSymbol = ResolveMethod(semanticModel, typeof(IDisposable), "Dispose");
            IMethodSymbol myDisposableDisposeMethodSymbol = ResolveMethod(semanticModel, typeof(MyDisposable), "Dispose");

            bool result1 = ImplementsInterfaceMember(dictionaryMethodSymbol, idictionaryAddMethodSymbol);
            bool result2 = ImplementsInterfaceMember(dictionaryMethodSymbol, idictionaryGetItemMethodSymbol);

            bool result3 = ImplementsInterfaceMember(dictionaryStringObjectMethodSymbol, idictionaryAddMethodSymbol);
            bool result4 = ImplementsInterfaceMember(dictionaryStringObjectMethodSymbol, idictionaryGetItemMethodSymbol);

            bool result5 = ImplementsInterfaceMember(dictionaryStringObjectMethodSymbol, idictionaryAddStringObjectMethodSymbol);
            bool result6 = ImplementsInterfaceMember(dictionaryStringObjectMethodSymbol, idictionaryAddStringStringMethodSymbol);

            bool result7 = ImplementsInterfaceMember(myDisposableDisposeMethodSymbol, idisposableDisposeMethodSymbol);
        }

        private static bool ImplementsInterfaceMember(IMethodSymbol implementationMethod, IMethodSymbol interfaceMethod)
        {
            if (!IsOpenMethod(interfaceMethod))
            {
                if (implementationMethod.Equals(implementationMethod.ContainingType.FindImplementationForInterfaceMember(interfaceMethod)))
                {
                    return true;
                }
            }
            else
            {
                INamedTypeSymbol interfaceTypeSymbol = interfaceMethod.ContainingType;
                INamedTypeSymbol interfaceConstructedFromTypeSymbol = interfaceTypeSymbol.ConstructedFrom;

                INamedTypeSymbol implementationTypeSymbol = implementationMethod.ContainingType;
                var implementedInterfaces = implementationTypeSymbol.AllInterfaces.Where(i => i.ConstructedFrom.Equals(interfaceConstructedFromTypeSymbol));

                foreach (var implementedInterface in implementedInterfaces)
                {
                    foreach (var implementedInterfaceMember in implementedInterface.GetMembers(interfaceMethod.Name))
                    {
                        if (implementedInterfaceMember.OriginalDefinition.Equals(interfaceMethod))
                        {
                            var exactImplementedInterfaceMember = implementationMethod.ContainingType.FindImplementationForInterfaceMember(implementedInterfaceMember);
                            if (implementationMethod.Equals(exactImplementedInterfaceMember))
                            {
                                return true;
                            }
                        }
                    }
                }
            }

            return false;
        }

        private static bool IsOpenMethod(IMethodSymbol method)
        {
            bool result = method.OriginalDefinition.Equals(method);
            return result;
        }

        private ITypeSymbol ResolveType(SemanticModel semanticModel, Type type)
        {
            string[] names = type.FullName.Split(new[] { '.', '+' }, StringSplitOptions.RemoveEmptyEntries);

            INamespaceOrTypeSymbol scope = null;
            for (int i = 0; i != names.Count(); ++i)
            {
                string metadataName = names[i];
                string name = metadataName;
                int index = name.IndexOf('`');
                int numberOfGenericTypes = 0;
                if (index != -1)
                {
                    string sNumber = name.Substring(index + 1);
                    if (!int.TryParse(sNumber, out numberOfGenericTypes))
                    {
                        return null;
                    }
                    name = name.Substring(0, index);
                }

                IEnumerable<ISymbol> symbols;
                if (i == 0)
                {
                    symbols = semanticModel.LookupNamespacesAndTypes(0, scope, name);
                }
                else
                {
                    symbols = scope.GetMembers(name).Where(m => m.Kind == SymbolKind.Namespace || m.Kind == SymbolKind.NamedType);
                }

                if (numberOfGenericTypes != 0)
                {
                    symbols = symbols.Where(s => s.MetadataName == metadataName);
                }
                if (symbols.Count() == 1)
                {
                    scope = (INamespaceOrTypeSymbol)symbols.First();
                }
                else
                {
                    scope = null;
                    break;
                }
            }

            return (ITypeSymbol)scope;
        }

        private ITypeSymbol ResolveType(SemanticModel semanticModel, Type type, params Type[] typeParameters)
        {
            ITypeSymbol typeSymbol = ResolveType(semanticModel, type);
            if (typeSymbol == null)
            {
                return null;
            }

            ITypeSymbol[] typeParametersSymbols = new ITypeSymbol[typeParameters.Length];
            for (int i = 0; i != typeParameters.Length; ++i)
            {
                ITypeSymbol typeParameterSymbol = ResolveType(semanticModel, typeParameters[i]);
                if (typeParameterSymbol == null)
                {
                    return null;
                }
                typeParametersSymbols[i] = typeParameterSymbol;
            }

            INamedTypeSymbol constructedTypeSymbol = ((INamedTypeSymbol)typeSymbol).Construct(typeParametersSymbols);
            return constructedTypeSymbol;
        }

        public IMethodSymbol ResolveMethod(SemanticModel semanticModel, Type type, string methodName)
        {
            ITypeSymbol typeSymbol = ResolveType(semanticModel, type);
            if (typeSymbol == null)
            {
                return null;
            }

            var members = typeSymbol.GetMembers(methodName);
            if (members.Length == 1
                && members[0] is IMethodSymbol)
            {
                return members[0] as IMethodSymbol;
            }

            return null;
        }

        public IMethodSymbol ResolveMethod(SemanticModel semanticModel, Type type, Type[] typeParameters, string methodName)
        {
            ITypeSymbol typeSymbol = ResolveType(semanticModel, type, typeParameters);
            if (typeSymbol == null)
            {
                return null;
            }

            var members = typeSymbol.GetMembers(methodName);
            if (members.Length == 1
                && members[0] is IMethodSymbol)
            {
                return members[0] as IMethodSymbol;
            }

            return null;
        }
    }
}