// Lean compiler output
// Module: Lake.Util.Binder
// Imports: public import Lean.Parser.Term meta import Lean.Parser.Term
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t);
extern lean_object* l_Lean_Parser_Term_binderIdent;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeTermArgument___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeTermArgument___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeTermArgument___closed__0 = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeTermArgument = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeEllipsisArgument = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeNamedArgumentArgument = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
static const lean_string_object l_Lake_mkHoleFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_mkHoleFrom___closed__0 = (const lean_object*)&l_Lake_mkHoleFrom___closed__0_value;
static const lean_string_object l_Lake_mkHoleFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_mkHoleFrom___closed__1 = (const lean_object*)&l_Lake_mkHoleFrom___closed__1_value;
static const lean_string_object l_Lake_mkHoleFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_mkHoleFrom___closed__2 = (const lean_object*)&l_Lake_mkHoleFrom___closed__2_value;
static const lean_string_object l_Lake_mkHoleFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lake_mkHoleFrom___closed__3 = (const lean_object*)&l_Lake_mkHoleFrom___closed__3_value;
static const lean_ctor_object l_Lake_mkHoleFrom___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_mkHoleFrom___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_mkHoleFrom___closed__4_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_mkHoleFrom___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_mkHoleFrom___closed__4_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_mkHoleFrom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_mkHoleFrom___closed__4_value_aux_2),((lean_object*)&l_Lake_mkHoleFrom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lake_mkHoleFrom___closed__4 = (const lean_object*)&l_Lake_mkHoleFrom___closed__4_value;
static const lean_string_object l_Lake_mkHoleFrom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lake_mkHoleFrom___closed__5 = (const lean_object*)&l_Lake_mkHoleFrom___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lake_instCoeHoleTerm = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeHoleBinderIdent = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeIdentBinderIdent = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeBinderIdentFunBinder = (const lean_object*)&l_Lake_instCoeTermArgument___closed__0_value;
static const lean_closure_object l_Lake_binder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_binderIdent_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_binder_formatter___closed__0 = (const lean_object*)&l_Lake_binder_formatter___closed__0_value;
static const lean_closure_object l_Lake_binder_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_bracketedBinder_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_binder_formatter___closed__1 = (const lean_object*)&l_Lake_binder_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_binder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_binderIdent_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_binder_parenthesizer___closed__0 = (const lean_object*)&l_Lake_binder_parenthesizer___closed__0_value;
static const lean_closure_object l_Lake_binder_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_binder_parenthesizer___closed__1 = (const lean_object*)&l_Lake_binder_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_binder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_binder___closed__0;
static lean_once_cell_t l_Lake_binder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_binder___closed__1;
LEAN_EXPORT lean_object* l_Lake_binder;
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeBinderIdentBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeBinderIdentBinder___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeBinderIdentBinder___closed__0 = (const lean_object*)&l_Lake_instCoeBinderIdentBinder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeBinderIdentBinder = (const lean_object*)&l_Lake_instCoeBinderIdentBinder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeBracketedBinderBinder = (const lean_object*)&l_Lake_instCoeBinderIdentBinder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeBinderDeclBinder = (const lean_object*)&l_Lake_instCoeBinderIdentBinder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeDepArrowTerm = (const lean_object*)&l_Lake_instCoeBinderIdentBinder___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedBinderSyntaxView_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedBinderSyntaxView_default = (const lean_object*)&l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedBinderSyntaxView = (const lean_object*)&l_Lake_instInhabitedBinderSyntaxView_default___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprBinderSyntaxView_repr_spec__1(lean_object*);
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__13_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__16_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17_value;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "modifier\?"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__18_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20;
static const lean_string_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22;
static lean_once_cell_t l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24_value;
static const lean_ctor_object l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__21_value)}};
static const lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25_value;
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBinderSyntaxView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBinderSyntaxView_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBinderSyntaxView___closed__0 = (const lean_object*)&l_Lake_instReprBinderSyntaxView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBinderSyntaxView = (const lean_object*)&l_Lake_instReprBinderSyntaxView___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "identifier or `_` expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_expandBinderIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lake_expandBinderIdent___closed__0 = (const lean_object*)&l_Lake_expandBinderIdent___closed__0_value;
static lean_once_cell_t l_Lake_expandBinderIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_expandBinderIdent___closed__1;
static const lean_ctor_object l_Lake_expandBinderIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_expandBinderIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lake_expandBinderIdent___closed__2 = (const lean_object*)&l_Lake_expandBinderIdent___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_expandBinderCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lake_expandBinderCore___closed__0 = (const lean_object*)&l_Lake_expandBinderCore___closed__0_value;
static const lean_ctor_object l_Lake_expandBinderCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__1_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__1_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__1_value_aux_2),((lean_object*)&l_Lake_expandBinderCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lake_expandBinderCore___closed__1 = (const lean_object*)&l_Lake_expandBinderCore___closed__1_value;
static const lean_string_object l_Lake_expandBinderCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l_Lake_expandBinderCore___closed__2 = (const lean_object*)&l_Lake_expandBinderCore___closed__2_value;
static const lean_ctor_object l_Lake_expandBinderCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__3_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__3_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__3_value_aux_2),((lean_object*)&l_Lake_expandBinderCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l_Lake_expandBinderCore___closed__3 = (const lean_object*)&l_Lake_expandBinderCore___closed__3_value;
static const lean_string_object l_Lake_expandBinderCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "strictImplicitBinder"};
static const lean_object* l_Lake_expandBinderCore___closed__4 = (const lean_object*)&l_Lake_expandBinderCore___closed__4_value;
static const lean_ctor_object l_Lake_expandBinderCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__5_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__5_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__5_value_aux_2),((lean_object*)&l_Lake_expandBinderCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 223, 215, 186, 222, 17, 242, 189)}};
static const lean_object* l_Lake_expandBinderCore___closed__5 = (const lean_object*)&l_Lake_expandBinderCore___closed__5_value;
static const lean_string_object l_Lake_expandBinderCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_Lake_expandBinderCore___closed__6 = (const lean_object*)&l_Lake_expandBinderCore___closed__6_value;
static const lean_ctor_object l_Lake_expandBinderCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__7_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__7_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_expandBinderCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_expandBinderCore___closed__7_value_aux_2),((lean_object*)&l_Lake_expandBinderCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l_Lake_expandBinderCore___closed__7 = (const lean_object*)&l_Lake_expandBinderCore___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_expandBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_expandBinder___closed__0 = (const lean_object*)&l_Lake_expandBinder___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__0 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__0_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__1 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__1_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__2 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__2_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__3 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__3_value;
static lean_once_cell_t l_Lake_BinderSyntaxView_mkBinder___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__4;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__5 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__5_value;
static const lean_array_object l_Lake_BinderSyntaxView_mkBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__6 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__6_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__7 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__7_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__8 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__8_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__9 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__9_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__10 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__10_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__11 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__11_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__12 = (const lean_object*)&l_Lake_BinderSyntaxView_mkBinder___closed__12_value;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object*);
static const lean_string_object l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "depArrow"};
static const lean_object* l_Lake_BinderSyntaxView_mkDepArrow___closed__0 = (const lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value_aux_2),((lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 137, 180, 163, 158, 211, 191, 168)}};
static const lean_object* l_Lake_BinderSyntaxView_mkDepArrow___closed__1 = (const lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__1_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkDepArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l_Lake_BinderSyntaxView_mkDepArrow___closed__2 = (const lean_object*)&l_Lake_BinderSyntaxView_mkDepArrow___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "UnhygienicMain"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__0 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 242, 144, 140, 56, 85, 78)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__1 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__1_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__2 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value_aux_2),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__3 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__3_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__4 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value_aux_2),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__5 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__5_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__6 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__7 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__7_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__8 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__8_value;
static lean_once_cell_t l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__9;
static lean_once_cell_t l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__10;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__11 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BinderSyntaxView"};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__12 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__11_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value_aux_0),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__12_value),LEAN_SCALAR_PTR_LITERAL(179, 223, 200, 222, 123, 238, 152, 251)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__13 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__13_value)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__14 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__15 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__15_value)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__16 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__17 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__17_value)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__18 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__19 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__16_value),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__19_value)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__20 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkFunBinder___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__14_value),((lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__20_value)}};
static const lean_object* l_Lake_BinderSyntaxView_mkFunBinder___closed__21 = (const lean_object*)&l_Lake_BinderSyntaxView_mkFunBinder___closed__21_value;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object*);
static const lean_string_object l_Lake_BinderSyntaxView_mkArgument___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__0 = (const lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__0_value;
static const lean_ctor_object l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_mkHoleFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_0),((lean_object*)&l_Lake_mkHoleFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_1),((lean_object*)&l_Lake_mkHoleFrom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_BinderSyntaxView_mkArgument___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__1_value_aux_2),((lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__1 = (const lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__1_value;
static const lean_string_object l_Lake_BinderSyntaxView_mkArgument___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__2 = (const lean_object*)&l_Lake_BinderSyntaxView_mkArgument___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0(lean_object* v_s_1_){
_start:
{
lean_inc(v_s_1_);
return v_s_1_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___lam__0___boxed(lean_object* v_s_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lake_instCoeTermArgument___lam__0(v_s_2_);
lean_dec(v_s_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object* v_ref_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_19_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_20_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__5));
v___x_21_ = 0;
v___x_22_ = l_Lean_mkAtomFrom(v_ref_18_, v___x_20_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_mk_empty_array_with_capacity(v___x_23_);
v___x_25_ = lean_array_push(v___x_24_, v___x_22_);
v___x_26_ = lean_box(2);
v___x_27_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_19_);
lean_ctor_set(v___x_27_, 2, v___x_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object* v_ref_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_mkHoleFrom(v_ref_28_);
lean_dec(v_ref_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((lean_object*)(l_Lake_binder_formatter___closed__0));
v___x_44_ = ((lean_object*)(l_Lake_binder_formatter___closed__1));
v___x_45_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_43_, v___x_44_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_formatter___boxed(lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_binder_formatter(v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((lean_object*)(l_Lake_binder_parenthesizer___closed__0));
v___x_62_ = ((lean_object*)(l_Lake_binder_parenthesizer___closed__1));
v___x_63_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_61_, v___x_62_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer___boxed(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lake_binder_parenthesizer(v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
static lean_object* _init_l_Lake_binder___closed__0(void){
_start:
{
uint8_t v___x_70_; lean_object* v___x_71_; 
v___x_70_ = 0;
v___x_71_ = l_Lean_Parser_Term_bracketedBinder(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lake_binder___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_Lake_binder___closed__0, &l_Lake_binder___closed__0_once, _init_l_Lake_binder___closed__0);
v___x_73_ = l_Lean_Parser_Term_binderIdent;
v___x_74_ = l_Lean_Parser_orelse(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lake_binder(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lake_binder___closed__1, &l_Lake_binder___closed__1_once, _init_l_Lake_binder___closed__1);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0(lean_object* v_stx_76_){
_start:
{
lean_inc(v_stx_76_);
return v_stx_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0___boxed(lean_object* v_stx_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lake_instCoeBinderIdentBinder___lam__0(v_stx_77_);
lean_dec(v_stx_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1));
return v___x_98_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_val_99_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v_x_96_, 1);
v___x_100_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3));
v___x_101_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_99_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_x_97_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___boxed(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(v_x_104_, v_x_105_);
lean_dec(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprBinderSyntaxView_repr_spec__1(lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_nat_to_int(v_a_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(7u);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(6u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(8u);
v___x_136_ = lean_nat_to_int(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(13u);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0));
v___x_147_ = lean_string_length(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg(lean_object* v_x_154_){
_start:
{
lean_object* v_ref_155_; lean_object* v_id_156_; lean_object* v_type_157_; uint8_t v_info_158_; lean_object* v_modifier_x3f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_ref_155_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_ref_155_);
v_id_156_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_id_156_);
v_type_157_ = lean_ctor_get(v_x_154_, 2);
lean_inc(v_type_157_);
v_info_158_ = lean_ctor_get_uint8(v_x_154_, sizeof(void*)*4);
v_modifier_x3f_159_ = lean_ctor_get(v_x_154_, 3);
lean_inc(v_modifier_x3f_159_);
lean_dec_ref(v_x_154_);
v___x_160_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5));
v___x_161_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6));
v___x_162_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_Lean_Syntax_instRepr_repr(v_ref_155_, v___x_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_161_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9));
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_box(1);
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11));
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_160_);
v___x_176_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12);
v___x_177_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_id_156_);
v___x_178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_166_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_169_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_171_);
v___x_183_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_160_);
v___x_186_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15);
v___x_187_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_type_157_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_166_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_185_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_169_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_171_);
v___x_193_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17));
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_160_);
v___x_196_ = l_Lean_instReprBinderInfo_repr(v_info_158_, v___x_163_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_186_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_166_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_195_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_169_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_171_);
v___x_202_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19));
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_160_);
v___x_205_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20);
v___x_206_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(v_modifier_x3f_159_, v___x_163_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_166_);
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_204_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23);
v___x_211_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24));
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_209_);
v___x_213_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25));
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_210_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_166_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lake_instReprBinderSyntaxView_repr___redArg(v_x_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___boxed(lean_object* v_x_220_, lean_object* v_prec_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_instReprBinderSyntaxView_repr(v_x_220_, v_prec_221_);
lean_dec(v_prec_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object* v_ref_225_, lean_object* v_optType_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l_Lean_Syntax_isNone(v_optType_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Lean_Syntax_getArg(v_optType_226_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = l_Lean_Syntax_getArg(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = l_Lake_mkHoleFrom(v_ref_225_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object* v_ref_233_, lean_object* v_optType_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lake_expandOptType(v_ref_233_, v_optType_234_);
lean_dec(v_optType_234_);
lean_dec(v_ref_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(size_t v_sz_240_, size_t v_i_241_, lean_object* v_bs_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_241_, v_sz_240_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_bs_242_);
lean_ctor_set(v___x_246_, 1, v___y_244_);
return v___x_246_;
}
else
{
lean_object* v_v_247_; lean_object* v___x_248_; lean_object* v_bs_x27_249_; lean_object* v_a_251_; lean_object* v_a_252_; lean_object* v_k_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_v_247_ = lean_array_uget(v_bs_242_, v_i_241_);
v___x_248_ = lean_unsigned_to_nat(0u);
v_bs_x27_249_ = lean_array_uset(v_bs_242_, v_i_241_, v___x_248_);
lean_inc(v_v_247_);
v_k_257_ = l_Lean_Syntax_getKind(v_v_247_);
v___x_258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1));
v___x_259_ = lean_name_eq(v_k_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_261_ = lean_name_eq(v_k_257_, v___x_260_);
lean_dec(v_k_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2));
v___x_263_ = l_Lean_Macro_throwErrorAt___redArg(v_v_247_, v___x_262_, v___y_243_, v___y_244_);
lean_dec(v_v_247_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_a_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
v_a_265_ = lean_ctor_get(v___x_263_, 1);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_263_, 2);
v_a_251_ = v_a_264_;
v_a_252_ = v_a_265_;
goto v___jp_250_;
}
else
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_bs_x27_249_);
v_a_266_ = lean_ctor_get(v___x_263_, 0);
v_a_267_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_263_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_inc(v_a_266_);
lean_dec(v___x_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_266_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
v_a_251_ = v_v_247_;
v_a_252_ = v___y_244_;
goto v___jp_250_;
}
}
else
{
lean_dec(v_k_257_);
v_a_251_ = v_v_247_;
v_a_252_ = v___y_244_;
goto v___jp_250_;
}
v___jp_250_:
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_add(v_i_241_, v___x_253_);
v___x_255_ = lean_array_uset(v_bs_x27_249_, v_i_241_, v_a_251_);
v_i_241_ = v___x_254_;
v_bs_242_ = v___x_255_;
v___y_244_ = v_a_252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___boxed(lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_bs_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
size_t v_sz_boxed_280_; size_t v_i_boxed_281_; lean_object* v_res_282_; 
v_sz_boxed_280_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_281_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_boxed_280_, v_i_boxed_281_, v_bs_277_, v___y_278_, v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object* v_ids_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_286_ = l_Lean_Syntax_getArgs(v_ids_283_);
v_sz_287_ = lean_array_size(v___x_286_);
v___x_288_ = ((size_t)0ULL);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_287_, v___x_288_, v___x_286_, v_a_284_, v_a_285_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object* v_ids_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lake_getBinderIds(v_ids_290_, v_a_291_, v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_ids_290_);
return v_res_293_;
}
}
static lean_object* _init_l_Lake_expandBinderIdent___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__0));
v___x_296_ = l_String_toRawSubstring_x27(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object* v_stx_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
lean_inc(v_stx_299_);
v___x_303_ = l_Lean_Syntax_isOfKind(v_stx_299_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_stx_299_);
lean_ctor_set(v___x_304_, 1, v_a_301_);
return v___x_304_;
}
else
{
lean_object* v_quotContext_305_; lean_object* v_currMacroScope_306_; lean_object* v_ref_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_stx_299_);
v_quotContext_305_ = lean_ctor_get(v_a_300_, 1);
v_currMacroScope_306_ = lean_ctor_get(v_a_300_, 2);
v_ref_307_ = lean_ctor_get(v_a_300_, 5);
v___x_308_ = 0;
v___x_309_ = l_Lean_SourceInfo_fromRef(v_ref_307_, v___x_308_);
v___x_310_ = lean_obj_once(&l_Lake_expandBinderIdent___closed__1, &l_Lake_expandBinderIdent___closed__1_once, _init_l_Lake_expandBinderIdent___closed__1);
v___x_311_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__2));
lean_inc(v_currMacroScope_306_);
lean_inc(v_quotContext_305_);
v___x_312_ = l_Lean_addMacroScope(v_quotContext_305_, v___x_311_, v_currMacroScope_306_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_309_);
lean_ctor_set(v___x_314_, 1, v___x_310_);
lean_ctor_set(v___x_314_, 2, v___x_312_);
lean_ctor_set(v___x_314_, 3, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_301_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent___boxed(lean_object* v_stx_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_expandBinderIdent(v_stx_316_, v_a_317_, v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* v_stx_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_Syntax_isNone(v_stx_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_Lean_Syntax_getArg(v_stx_320_, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = l_Lake_mkHoleFrom(v_stx_320_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* v_stx_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lake_expandOptIdent(v_stx_325_);
lean_dec(v_stx_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* v_ref_327_, lean_object* v_stx_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = l_Lean_Syntax_getNumArgs(v_stx_328_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_nat_dec_eq(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = l_Lean_Syntax_getArg(v_stx_328_, v___x_332_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Lake_mkHoleFrom(v_ref_327_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* v_ref_335_, lean_object* v_stx_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lake_expandBinderType(v_ref_335_, v_stx_336_);
lean_dec(v_stx_336_);
lean_dec(v_ref_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* v_optBinderModifier_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Syntax_getOptional_x3f(v_optBinderModifier_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_val_341_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_val_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* v_optBinderModifier_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_expandBinderModifier(v_optBinderModifier_349_);
lean_dec(v_optBinderModifier_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(lean_object* v___x_351_, lean_object* v_stx_352_, lean_object* v_as_353_, size_t v_i_354_, size_t v_stop_355_, lean_object* v_b_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_eq(v_i_354_, v_stop_355_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_array_uget_borrowed(v_as_353_, v_i_354_);
lean_inc(v___x_360_);
v___x_361_ = l_Lake_expandBinderIdent(v___x_360_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; size_t v___x_369_; size_t v___x_370_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
v_a_363_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_361_, 2);
v___x_364_ = l_Lake_expandBinderType(v___x_360_, v___x_351_);
v___x_365_ = 1;
v___x_366_ = lean_box(0);
lean_inc(v_stx_352_);
v___x_367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_367_, 0, v_stx_352_);
lean_ctor_set(v___x_367_, 1, v_a_362_);
lean_ctor_set(v___x_367_, 2, v___x_364_);
lean_ctor_set(v___x_367_, 3, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*4, v___x_365_);
v___x_368_ = lean_array_push(v_b_356_, v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_354_, v___x_369_);
v_i_354_ = v___x_370_;
v_b_356_ = v___x_368_;
v___y_358_ = v_a_363_;
goto _start;
}
else
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_b_356_);
lean_dec(v_stx_352_);
v_a_372_ = lean_ctor_get(v___x_361_, 0);
v_a_373_ = lean_ctor_get(v___x_361_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v___x_361_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_stx_352_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_b_356_);
lean_ctor_set(v___x_381_, 1, v___y_358_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(lean_object* v___x_382_, lean_object* v_stx_383_, lean_object* v_as_384_, lean_object* v_i_385_, lean_object* v_stop_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
size_t v_i_boxed_390_; size_t v_stop_boxed_391_; lean_object* v_res_392_; 
v_i_boxed_390_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_stop_boxed_391_ = lean_unbox_usize(v_stop_386_);
lean_dec(v_stop_386_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_382_, v_stx_383_, v_as_384_, v_i_boxed_390_, v_stop_boxed_391_, v_b_387_, v___y_388_, v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec_ref(v_as_384_);
lean_dec(v___x_382_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(lean_object* v___x_393_, lean_object* v_stx_394_, lean_object* v___x_395_, lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
lean_inc(v___x_403_);
v___x_404_ = l_Lake_expandBinderIdent(v___x_403_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
v_a_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_404_, 2);
v___x_407_ = l_Lake_expandBinderType(v___x_403_, v___x_393_);
v___x_408_ = 0;
lean_inc(v___x_395_);
lean_inc(v_stx_394_);
v___x_409_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_409_, 0, v_stx_394_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
lean_ctor_set(v___x_409_, 2, v___x_407_);
lean_ctor_set(v___x_409_, 3, v___x_395_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*4, v___x_408_);
v___x_410_ = lean_array_push(v_b_399_, v___x_409_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_397_, v___x_411_);
v_i_397_ = v___x_412_;
v_b_399_ = v___x_410_;
v___y_401_ = v_a_406_;
goto _start;
}
else
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_b_399_);
lean_dec(v___x_395_);
lean_dec(v_stx_394_);
v_a_414_ = lean_ctor_get(v___x_404_, 0);
v_a_415_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_404_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_inc(v_a_414_);
lean_dec(v___x_404_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v___x_395_);
lean_dec(v_stx_394_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_b_399_);
lean_ctor_set(v___x_423_, 1, v___y_401_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(lean_object* v___x_424_, lean_object* v_stx_425_, lean_object* v___x_426_, lean_object* v_as_427_, lean_object* v_i_428_, lean_object* v_stop_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
size_t v_i_boxed_433_; size_t v_stop_boxed_434_; lean_object* v_res_435_; 
v_i_boxed_433_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_stop_boxed_434_ = lean_unbox_usize(v_stop_429_);
lean_dec(v_stop_429_);
v_res_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_424_, v_stx_425_, v___x_426_, v_as_427_, v_i_boxed_433_, v_stop_boxed_434_, v_b_430_, v___y_431_, v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_as_427_);
lean_dec(v___x_424_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(lean_object* v___x_436_, lean_object* v_stx_437_, lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
lean_inc(v___x_445_);
v___x_446_ = l_Lake_expandBinderIdent(v___x_445_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_a_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; size_t v___x_454_; size_t v___x_455_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
v_a_448_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_446_, 2);
v___x_449_ = l_Lake_expandBinderType(v___x_445_, v___x_436_);
v___x_450_ = 2;
v___x_451_ = lean_box(0);
lean_inc(v_stx_437_);
v___x_452_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_452_, 0, v_stx_437_);
lean_ctor_set(v___x_452_, 1, v_a_447_);
lean_ctor_set(v___x_452_, 2, v___x_449_);
lean_ctor_set(v___x_452_, 3, v___x_451_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*4, v___x_450_);
v___x_453_ = lean_array_push(v_b_441_, v___x_452_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_439_, v___x_454_);
v_i_439_ = v___x_455_;
v_b_441_ = v___x_453_;
v___y_443_ = v_a_448_;
goto _start;
}
else
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_b_441_);
lean_dec(v_stx_437_);
v_a_457_ = lean_ctor_get(v___x_446_, 0);
v_a_458_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_446_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_inc(v_a_457_);
lean_dec(v___x_446_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v_stx_437_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_b_441_);
lean_ctor_set(v___x_466_, 1, v___y_443_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(lean_object* v___x_467_, lean_object* v_stx_468_, lean_object* v_as_469_, lean_object* v_i_470_, lean_object* v_stop_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; lean_object* v_res_477_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_471_);
lean_dec(v_stop_471_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_467_, v_stx_468_, v_as_469_, v_i_boxed_475_, v_stop_boxed_476_, v_b_472_, v___y_473_, v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec_ref(v_as_469_);
lean_dec(v___x_467_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object* v_binders_502_, lean_object* v_stx_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Syntax_isIdent(v_stx_503_);
if (v___x_522_ == 0)
{
lean_object* v_k_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_inc(v_stx_503_);
v_k_523_ = l_Lean_Syntax_getKind(v_stx_503_);
v___x_524_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_525_ = lean_name_eq(v_k_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_527_ = lean_name_eq(v_k_523_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_529_ = lean_name_eq(v_k_523_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_531_ = lean_name_eq(v_k_523_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_533_ = lean_name_eq(v_k_523_, v___x_532_);
lean_dec(v_k_523_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_stx_503_);
lean_dec_ref(v_binders_502_);
v___x_534_ = l_Lean_Macro_throwUnsupported___redArg(v_a_505_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_id_537_; lean_object* v___x_538_; lean_object* v_a_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_553_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_535_);
v_id_537_ = l_Lake_expandOptIdent(v___x_536_);
lean_dec(v___x_536_);
v___x_538_ = l_Lake_expandBinderIdent(v_id_537_, v_a_504_, v_a_505_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_a_540_ = lean_ctor_get(v___x_538_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_553_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_553_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_553_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v_type_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_544_ = lean_unsigned_to_nat(2u);
v_type_545_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_544_);
v___x_546_ = 3;
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_548_, 0, v_stx_503_);
lean_ctor_set(v___x_548_, 1, v_a_539_);
lean_ctor_set(v___x_548_, 2, v_type_545_);
lean_ctor_set(v___x_548_, 3, v___x_547_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*4, v___x_546_);
v___x_549_ = lean_array_push(v_binders_502_, v___x_548_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_551_ = v___x_542_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_a_540_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_k_523_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_554_);
v___x_556_ = l_Lake_getBinderIds(v___x_555_, v_a_504_, v_a_505_);
lean_dec(v___x_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_573_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_a_558_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_573_ == 0)
{
v___x_560_ = v___x_556_;
v_isShared_561_ = v_isSharedCheck_573_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_573_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_array_get_size(v_a_557_);
v___x_564_ = lean_nat_dec_lt(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_a_557_);
lean_dec(v_stx_503_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_binders_502_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_binders_502_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_a_558_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
lean_del_object(v___x_560_);
v___x_568_ = lean_unsigned_to_nat(2u);
v___x_569_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_568_);
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_563_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_569_, v_stx_503_, v_a_557_, v___x_570_, v___x_571_, v_binders_502_, v_a_504_, v_a_558_);
lean_dec(v_a_557_);
lean_dec(v___x_569_);
return v___x_572_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_stx_503_);
lean_dec_ref(v_binders_502_);
v_a_574_ = lean_ctor_get(v___x_556_, 0);
v_a_575_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_556_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_dec(v___x_556_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_574_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_k_523_);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_583_);
v___x_585_ = l_Lake_getBinderIds(v___x_584_, v_a_504_, v_a_505_);
lean_dec(v___x_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_602_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_a_587_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_602_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_602_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_a_586_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v_a_586_);
lean_dec(v_stx_503_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_binders_502_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_binders_502_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_587_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
lean_del_object(v___x_589_);
v___x_597_ = lean_unsigned_to_nat(2u);
v___x_598_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_597_);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_592_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_598_, v_stx_503_, v_a_586_, v___x_599_, v___x_600_, v_binders_502_, v_a_504_, v_a_587_);
lean_dec(v_a_586_);
lean_dec(v___x_598_);
return v___x_601_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_stx_503_);
lean_dec_ref(v_binders_502_);
v_a_603_ = lean_ctor_get(v___x_585_, 0);
v_a_604_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_585_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_inc(v_a_603_);
lean_dec(v___x_585_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_k_523_);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_612_);
v___x_614_ = l_Lake_getBinderIds(v___x_613_, v_a_504_, v_a_505_);
lean_dec(v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_634_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_634_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_array_get_size(v_a_615_);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_624_; 
lean_dec(v_a_615_);
lean_dec(v_stx_503_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_binders_502_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_binders_502_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_a_616_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
lean_del_object(v___x_618_);
v___x_626_ = lean_unsigned_to_nat(2u);
v___x_627_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(3u);
v___x_629_ = l_Lean_Syntax_getArg(v_stx_503_, v___x_628_);
v___x_630_ = l_Lake_expandBinderModifier(v___x_629_);
lean_dec(v___x_629_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = lean_usize_of_nat(v___x_621_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_627_, v_stx_503_, v___x_630_, v_a_615_, v___x_631_, v___x_632_, v_binders_502_, v_a_504_, v_a_616_);
lean_dec(v_a_615_);
lean_dec(v___x_627_);
return v___x_633_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_stx_503_);
lean_dec_ref(v_binders_502_);
v_a_635_ = lean_ctor_get(v___x_614_, 0);
v_a_636_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_614_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_inc(v_a_635_);
lean_dec(v___x_614_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
else
{
lean_dec(v_k_523_);
goto v___jp_506_;
}
}
else
{
goto v___jp_506_;
}
v___jp_506_:
{
lean_object* v___x_507_; lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
lean_inc(v_stx_503_);
v___x_507_ = l_Lake_expandBinderIdent(v_stx_503_, v_a_504_, v_a_505_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_a_509_ = lean_ctor_get(v___x_507_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v___x_507_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_513_ = l_Lake_mkHoleFrom(v_stx_503_);
v___x_514_ = 0;
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_516_, 0, v_stx_503_);
lean_ctor_set(v___x_516_, 1, v_a_508_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
lean_ctor_set(v___x_516_, 3, v___x_515_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*4, v___x_514_);
v___x_517_ = lean_array_push(v_binders_502_, v___x_516_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_517_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_a_509_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore___boxed(lean_object* v_binders_644_, lean_object* v_stx_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lake_expandBinderCore(v_binders_644_, v_stx_645_, v_a_646_, v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object* v_stx_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_655_ = l_Lake_expandBinderCore(v___x_654_, v_stx_651_, v_a_652_, v_a_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder___boxed(lean_object* v_stx_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_expandBinder(v_stx_656_, v_a_657_, v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(lean_object* v_as_660_, size_t v_i_661_, size_t v_stop_662_, lean_object* v_b_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_eq(v_i_661_, v_stop_662_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_array_uget_borrowed(v_as_660_, v_i_661_);
lean_inc(v___x_667_);
v___x_668_ = l_Lake_expandBinderCore(v_b_663_, v___x_667_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_a_670_; size_t v___x_671_; size_t v___x_672_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
v_a_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_668_, 2);
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_add(v_i_661_, v___x_671_);
v_i_661_ = v___x_672_;
v_b_663_ = v_a_669_;
v___y_665_ = v_a_670_;
goto _start;
}
else
{
return v___x_668_;
}
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_b_663_);
lean_ctor_set(v___x_674_, 1, v___y_665_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(lean_object* v_as_675_, lean_object* v_i_676_, lean_object* v_stop_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
size_t v_i_boxed_681_; size_t v_stop_boxed_682_; lean_object* v_res_683_; 
v_i_boxed_681_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_stop_boxed_682_ = lean_unbox_usize(v_stop_677_);
lean_dec(v_stop_677_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_675_, v_i_boxed_681_, v_stop_boxed_682_, v_b_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec_ref(v_as_675_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* v_stxs_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_689_ = lean_array_get_size(v_stxs_684_);
v___x_690_ = lean_nat_dec_lt(v___x_687_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_688_);
lean_ctor_set(v___x_691_, 1, v_a_686_);
return v___x_691_;
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_689_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_684_, v___x_692_, v___x_693_, v___x_688_, v_a_685_, v_a_686_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* v_stxs_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lake_expandBinders(v_stxs_695_, v_a_696_, v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_stxs_695_);
return v_res_698_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__4(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Array_mkArray0___redArg();
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* v_x_714_){
_start:
{
uint8_t v_info_715_; 
v_info_715_ = lean_ctor_get_uint8(v_x_714_, sizeof(void*)*4);
switch(v_info_715_)
{
case 0:
{
lean_object* v_ref_716_; lean_object* v_id_717_; lean_object* v_type_718_; lean_object* v_modifier_x3f_719_; uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___y_732_; 
v_ref_716_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_ref_716_);
v_id_717_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_id_717_);
v_type_718_ = lean_ctor_get(v_x_714_, 2);
lean_inc(v_type_718_);
v_modifier_x3f_719_ = lean_ctor_get(v_x_714_, 3);
lean_inc(v_modifier_x3f_719_);
lean_dec_ref(v_x_714_);
v___x_720_ = 0;
v___x_721_ = l_Lean_SourceInfo_fromRef(v_ref_716_, v___x_720_);
lean_dec(v_ref_716_);
v___x_722_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_723_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_721_, 4);
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_726_ = l_Lean_Syntax_node1(v___x_721_, v___x_725_, v_id_717_);
v___x_727_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_721_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_Syntax_node2(v___x_721_, v___x_725_, v___x_728_, v_type_718_);
v___x_730_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkBinder___closed__4, &l_Lake_BinderSyntaxView_mkBinder___closed__4_once, _init_l_Lake_BinderSyntaxView_mkBinder___closed__4);
if (lean_obj_tag(v_modifier_x3f_719_) == 1)
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v_modifier_x3f_719_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v_modifier_x3f_719_, 1);
v___x_739_ = l_Array_mkArray1___redArg(v_val_738_);
v___y_732_ = v___x_739_;
goto v___jp_731_;
}
else
{
lean_object* v___x_740_; 
lean_dec(v_modifier_x3f_719_);
v___x_740_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__6));
v___y_732_ = v___x_740_;
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_733_ = l_Array_append___redArg(v___x_730_, v___y_732_);
lean_dec_ref(v___y_732_);
lean_inc_n(v___x_721_, 2);
v___x_734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_734_, 0, v___x_721_);
lean_ctor_set(v___x_734_, 1, v___x_725_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_721_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Syntax_node5(v___x_721_, v___x_722_, v___x_724_, v___x_726_, v___x_729_, v___x_734_, v___x_736_);
return v___x_737_;
}
}
case 1:
{
lean_object* v_ref_741_; lean_object* v_id_742_; lean_object* v_type_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_ref_741_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_ref_741_);
v_id_742_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_id_742_);
v_type_743_ = lean_ctor_get(v_x_714_, 2);
lean_inc(v_type_743_);
lean_dec_ref(v_x_714_);
v___x_744_ = 0;
v___x_745_ = l_Lean_SourceInfo_fromRef(v_ref_741_, v___x_744_);
lean_dec(v_ref_741_);
v___x_746_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_747_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_745_, 5);
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_750_ = l_Lean_Syntax_node1(v___x_745_, v___x_749_, v_id_742_);
v___x_751_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_745_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_Syntax_node2(v___x_745_, v___x_749_, v___x_752_, v_type_743_);
v___x_754_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_745_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_Syntax_node4(v___x_745_, v___x_746_, v___x_748_, v___x_750_, v___x_753_, v___x_755_);
return v___x_756_;
}
case 2:
{
lean_object* v_ref_757_; lean_object* v_id_758_; lean_object* v_type_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_ref_757_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_ref_757_);
v_id_758_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_id_758_);
v_type_759_ = lean_ctor_get(v_x_714_, 2);
lean_inc(v_type_759_);
lean_dec_ref(v_x_714_);
v___x_760_ = 0;
v___x_761_ = l_Lean_SourceInfo_fromRef(v_ref_757_, v___x_760_);
lean_dec(v_ref_757_);
v___x_762_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_763_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_761_, 5);
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_766_ = l_Lean_Syntax_node1(v___x_761_, v___x_765_, v_id_758_);
v___x_767_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_761_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_Syntax_node2(v___x_761_, v___x_765_, v___x_768_, v_type_759_);
v___x_770_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_761_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_Syntax_node4(v___x_761_, v___x_762_, v___x_764_, v___x_766_, v___x_769_, v___x_771_);
return v___x_772_;
}
default: 
{
lean_object* v_ref_773_; lean_object* v_id_774_; lean_object* v_type_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_ref_773_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_ref_773_);
v_id_774_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_id_774_);
v_type_775_ = lean_ctor_get(v_x_714_, 2);
lean_inc(v_type_775_);
lean_dec_ref(v_x_714_);
v___x_776_ = 0;
v___x_777_ = l_Lean_SourceInfo_fromRef(v_ref_773_, v___x_776_);
lean_dec(v_ref_773_);
v___x_778_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_779_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_777_, 4);
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_782_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_777_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_Syntax_node2(v___x_777_, v___x_781_, v_id_774_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_777_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_Syntax_node4(v___x_777_, v___x_778_, v___x_780_, v___x_784_, v_type_775_, v___x_786_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object* v_res_795_, lean_object* v_self_796_){
_start:
{
lean_object* v_ref_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_ref_797_ = lean_ctor_get(v_self_796_, 0);
v___x_798_ = 0;
v___x_799_ = l_Lean_SourceInfo_fromRef(v_ref_797_, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__1));
v___x_801_ = l_Lake_BinderSyntaxView_mkBinder(v_self_796_);
v___x_802_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__2));
lean_inc(v___x_799_);
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_799_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_Syntax_node3(v___x_799_, v___x_800_, v___x_801_, v___x_803_, v_res_795_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(lean_object* v_as_805_, size_t v_i_806_, size_t v_stop_807_, lean_object* v_b_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_eq(v_i_806_, v_stop_807_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; 
v___x_810_ = lean_array_uget_borrowed(v_as_805_, v_i_806_);
lean_inc(v___x_810_);
v___x_811_ = l_Lake_BinderSyntaxView_mkDepArrow(v_b_808_, v___x_810_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_i_806_, v___x_812_);
v_i_806_ = v___x_813_;
v_b_808_ = v___x_811_;
goto _start;
}
else
{
return v_b_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(lean_object* v_as_815_, lean_object* v_i_816_, lean_object* v_stop_817_, lean_object* v_b_818_){
_start:
{
size_t v_i_boxed_819_; size_t v_stop_boxed_820_; lean_object* v_res_821_; 
v_i_boxed_819_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_stop_boxed_820_ = lean_unbox_usize(v_stop_817_);
lean_dec(v_stop_817_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_815_, v_i_boxed_819_, v_stop_boxed_820_, v_b_818_);
lean_dec_ref(v_as_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object* v_binders_822_, lean_object* v_res_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_array_get_size(v_binders_822_);
v___x_826_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
return v_res_823_;
}
else
{
size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_825_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_822_, v___x_827_, v___x_828_, v_res_823_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object* v_binders_830_, lean_object* v_res_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lake_mkDepArrow(v_binders_830_, v_res_831_);
lean_dec_ref(v_binders_830_);
return v_res_832_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__8));
v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_854_ = l_Lean_firstFrontendMacroScope;
v___x_855_ = lean_box(0);
v___x_856_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__1));
v___x_857_ = l_Lean_addMacroScope(v___x_856_, v___x_855_, v___x_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object* v_x_883_){
_start:
{
lean_object* v_ref_884_; lean_object* v_id_885_; lean_object* v_type_886_; uint8_t v_info_887_; lean_object* v___x_888_; lean_object* v_ref_889_; 
v_ref_884_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_ref_884_);
v_id_885_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_id_885_);
v_type_886_ = lean_ctor_get(v_x_883_, 2);
lean_inc(v_type_886_);
v_info_887_ = lean_ctor_get_uint8(v_x_883_, sizeof(void*)*4);
lean_dec_ref(v_x_883_);
v___x_888_ = lean_box(0);
v_ref_889_ = l_Lean_replaceRef(v_ref_884_, v___x_888_);
lean_dec(v_ref_884_);
switch(v_info_887_)
{
case 0:
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_890_ = 0;
v___x_891_ = l_Lean_SourceInfo_fromRef(v_ref_889_, v___x_890_);
lean_dec(v_ref_889_);
v___x_892_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__3));
v___x_893_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__5));
v___x_894_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_891_, 7);
v___x_895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_891_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__7));
v___x_897_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__9, &l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9);
v___x_898_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__10, &l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10);
v___x_899_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__21));
v___x_900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_900_, 0, v___x_891_);
lean_ctor_set(v___x_900_, 1, v___x_897_);
lean_ctor_set(v___x_900_, 2, v___x_898_);
lean_ctor_set(v___x_900_, 3, v___x_899_);
v___x_901_ = l_Lean_Syntax_node1(v___x_891_, v___x_896_, v___x_900_);
v___x_902_ = l_Lean_Syntax_node2(v___x_891_, v___x_893_, v___x_895_, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_891_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_906_ = l_Lean_Syntax_node1(v___x_891_, v___x_905_, v_type_886_);
v___x_907_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_891_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_Syntax_node5(v___x_891_, v___x_892_, v___x_902_, v_id_885_, v___x_904_, v___x_906_, v___x_908_);
return v___x_909_;
}
case 1:
{
uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_910_ = 0;
v___x_911_ = l_Lean_SourceInfo_fromRef(v_ref_889_, v___x_910_);
lean_dec(v_ref_889_);
v___x_912_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_913_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_911_, 5);
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_911_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_916_ = l_Lean_Syntax_node1(v___x_911_, v___x_915_, v_id_885_);
v___x_917_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_911_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_Syntax_node2(v___x_911_, v___x_915_, v___x_918_, v_type_886_);
v___x_920_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_911_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_Syntax_node4(v___x_911_, v___x_912_, v___x_914_, v___x_916_, v___x_919_, v___x_921_);
return v___x_922_;
}
case 2:
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_923_ = 0;
v___x_924_ = l_Lean_SourceInfo_fromRef(v_ref_889_, v___x_923_);
lean_dec(v_ref_889_);
v___x_925_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_926_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_924_, 5);
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_924_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_929_ = l_Lean_Syntax_node1(v___x_924_, v___x_928_, v_id_885_);
v___x_930_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_924_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_Syntax_node2(v___x_924_, v___x_928_, v___x_931_, v_type_886_);
v___x_933_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_924_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_Syntax_node4(v___x_924_, v___x_925_, v___x_927_, v___x_929_, v___x_932_, v___x_934_);
return v___x_935_;
}
default: 
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_936_ = 0;
v___x_937_ = l_Lean_SourceInfo_fromRef(v_ref_889_, v___x_936_);
lean_dec(v_ref_889_);
v___x_938_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_939_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_937_, 4);
v___x_940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_937_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_942_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_937_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_Syntax_node2(v___x_937_, v___x_941_, v_id_885_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_937_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_Syntax_node4(v___x_937_, v___x_938_, v___x_940_, v___x_944_, v_type_886_, v___x_946_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* v_x_955_){
_start:
{
lean_object* v_ref_956_; lean_object* v_id_957_; lean_object* v___x_958_; lean_object* v_ref_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_ref_956_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_ref_956_);
v_id_957_ = lean_ctor_get(v_x_955_, 1);
lean_inc_n(v_id_957_, 2);
lean_dec_ref(v_x_955_);
v___x_958_ = lean_box(0);
v_ref_959_ = l_Lean_replaceRef(v_ref_956_, v___x_958_);
lean_dec(v_ref_956_);
v___x_960_ = 0;
v___x_961_ = l_Lean_SourceInfo_fromRef(v_ref_959_, v___x_960_);
lean_dec(v_ref_959_);
v___x_962_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__1));
v___x_963_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_961_, 3);
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__2));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_Syntax_node5(v___x_961_, v___x_962_, v___x_964_, v_id_957_, v___x_966_, v_id_957_, v___x_968_);
return v___x_969_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_binder = _init_l_Lake_binder();
lean_mark_persistent(l_Lake_binder);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Binder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Binder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Binder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Binder(builtin);
}
#ifdef __cplusplus
}
#endif
