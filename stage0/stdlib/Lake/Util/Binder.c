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
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "identifier or `_` expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
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
lean_object* l_Lake_binder_formatter(lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = ((lean_object*)(l_Lake_binder_formatter___closed__0));
v___x_44_ = ((lean_object*)(l_Lake_binder_formatter___closed__1));
v___x_45_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_43_, v___x_44_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Lake_binder_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_38_ = stack[0].m_obj;
lean_object* v_a_39_ = stack[1].m_obj;
lean_object* v_a_40_ = stack[2].m_obj;
lean_object* v_a_41_ = stack[3].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lake_binder_formatter(v_a_38_, v_a_39_, v_a_40_, v_a_41_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lake_binder_formatter___boxed(lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lake_binder_formatter(v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_52_;
}
}
lean_object* l_Lake_binder_parenthesizer(lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = ((lean_object*)(l_Lake_binder_parenthesizer___closed__0));
v___x_63_ = ((lean_object*)(l_Lake_binder_parenthesizer___closed__1));
v___x_64_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_62_, v___x_63_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lake_binder_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_a_59_ = stack[2].m_obj;
lean_object* v_a_60_ = stack[3].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lake_binder_parenthesizer(v_a_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer___boxed(lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lake_binder_parenthesizer(v_a_66_, v_a_67_, v_a_68_, v_a_69_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_71_;
}
}
static lean_object* _init_l_Lake_binder___closed__0(void){
_start:
{
uint8_t v___x_72_; lean_object* v___x_73_; 
v___x_72_ = 0;
v___x_73_ = l_Lean_Parser_Term_bracketedBinder(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_binder___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_Lake_binder___closed__0, &l_Lake_binder___closed__0_once, _init_l_Lake_binder___closed__0);
v___x_75_ = l_Lean_Parser_Term_binderIdent;
v___x_76_ = l_Lean_Parser_orelse(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lake_binder(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lake_binder___closed__1, &l_Lake_binder___closed__1_once, _init_l_Lake_binder___closed__1);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0(lean_object* v_stx_78_){
_start:
{
lean_inc(v_stx_78_);
return v_stx_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentBinder___lam__0___boxed(lean_object* v_stx_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_instCoeBinderIdentBinder___lam__0(v_stx_79_);
lean_dec(v_stx_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_100_; 
v___x_100_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__1));
return v___x_100_;
}
else
{
lean_object* v_val_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_val_101_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v_x_98_, 1);
v___x_102_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___closed__3));
v___x_103_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_val_101_);
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Repr_addAppParen(v___x_104_, v_x_99_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(v_x_106_, v_x_107_);
lean_dec(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprBinderSyntaxView_repr_spec__1(lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_to_int(v_a_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(7u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(6u);
v___x_133_ = lean_nat_to_int(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(8u);
v___x_138_ = lean_nat_to_int(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(13u);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__0));
v___x_149_ = lean_string_length(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__22);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___redArg(lean_object* v_x_156_){
_start:
{
lean_object* v_ref_157_; lean_object* v_id_158_; lean_object* v_type_159_; uint8_t v_info_160_; lean_object* v_modifier_x3f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_ref_157_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_ref_157_);
v_id_158_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_id_158_);
v_type_159_ = lean_ctor_get(v_x_156_, 2);
lean_inc(v_type_159_);
v_info_160_ = lean_ctor_get_uint8(v_x_156_, sizeof(void*)*4);
v_modifier_x3f_161_ = lean_ctor_get(v_x_156_, 3);
lean_inc(v_modifier_x3f_161_);
lean_dec_ref(v_x_156_);
v___x_162_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__5));
v___x_163_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__6));
v___x_164_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__7);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Lean_Syntax_instRepr_repr(v_ref_157_, v___x_165_);
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_164_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_168_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_163_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__9));
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_box(1);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__11));
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_162_);
v___x_178_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__12);
v___x_179_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_id_158_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_168_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_177_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_171_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_173_);
v___x_185_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__14));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_162_);
v___x_188_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__15);
v___x_189_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_type_159_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_168_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_187_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_171_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_173_);
v___x_195_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__17));
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_162_);
v___x_198_ = l_Lean_instReprBinderInfo_repr(v_info_160_, v___x_165_);
v___x_199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_188_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_168_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_197_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_171_);
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_173_);
v___x_204_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__19));
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_162_);
v___x_207_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__20);
v___x_208_ = l_Option_repr___at___00Lake_instReprBinderSyntaxView_repr_spec__0(v_modifier_x3f_161_, v___x_165_);
v___x_209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_168_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_206_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_obj_once(&l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23, &l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23_once, _init_l_Lake_instReprBinderSyntaxView_repr___redArg___closed__23);
v___x_213_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__24));
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_211_);
v___x_215_ = ((lean_object*)(l_Lake_instReprBinderSyntaxView_repr___redArg___closed__25));
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_212_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v___x_168_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr(lean_object* v_x_219_, lean_object* v_prec_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lake_instReprBinderSyntaxView_repr___redArg(v_x_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBinderSyntaxView_repr___boxed(lean_object* v_x_222_, lean_object* v_prec_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lake_instReprBinderSyntaxView_repr(v_x_222_, v_prec_223_);
lean_dec(v_prec_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object* v_ref_227_, lean_object* v_optType_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Lean_Syntax_isNone(v_optType_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_Syntax_getArg(v_optType_228_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = l_Lean_Syntax_getArg(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = l_Lake_mkHoleFrom(v_ref_227_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object* v_ref_235_, lean_object* v_optType_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lake_expandOptType(v_ref_235_, v_optType_236_);
lean_dec(v_optType_236_);
lean_dec(v_ref_235_);
return v_res_237_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(size_t v_sz_242_, size_t v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_bs_244_);
lean_ctor_set(v___x_248_, 1, v___y_246_);
return v___x_248_;
}
else
{
lean_object* v_v_249_; lean_object* v___x_250_; lean_object* v_bs_x27_251_; lean_object* v_a_253_; lean_object* v_a_254_; uint8_t v___y_260_; lean_object* v_k_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_v_249_ = lean_array_uget(v_bs_244_, v_i_243_);
v___x_250_ = lean_unsigned_to_nat(0u);
v_bs_x27_251_ = lean_array_uset(v_bs_244_, v_i_243_, v___x_250_);
lean_inc(v_v_249_);
v_k_274_ = l_Lean_Syntax_getKind(v_v_249_);
v___x_275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2));
v___x_276_ = lean_name_eq(v_k_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_278_ = lean_name_eq(v_k_274_, v___x_277_);
lean_dec(v_k_274_);
v___y_260_ = v___x_278_;
goto v___jp_259_;
}
else
{
lean_dec(v_k_274_);
v___y_260_ = v___x_276_;
goto v___jp_259_;
}
v___jp_252_:
{
size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_243_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_251_, v_i_243_, v_a_253_);
v_i_243_ = v___x_256_;
v_bs_244_ = v___x_257_;
v___y_246_ = v_a_254_;
goto _start;
}
v___jp_259_:
{
if (v___y_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0));
v___x_262_ = l_Lean_Macro_throwErrorAt___redArg(v_v_249_, v___x_261_, v___y_245_, v___y_246_);
lean_dec(v_v_249_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v_a_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
v_a_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_262_, 2);
v_a_253_ = v_a_263_;
v_a_254_ = v_a_264_;
goto v___jp_252_;
}
else
{
lean_object* v_a_265_; lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_bs_x27_251_);
v_a_265_ = lean_ctor_get(v___x_262_, 0);
v_a_266_ = lean_ctor_get(v___x_262_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_262_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_inc(v_a_265_);
lean_dec(v___x_262_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_265_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
v_a_253_ = v_v_249_;
v_a_254_ = v___y_246_;
goto v___jp_252_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_242_ = stack[0].m_num;
size_t v_i_243_ = stack[1].m_num;
lean_object* v_bs_244_ = stack[2].m_obj;
lean_object* v___y_245_ = stack[3].m_obj;
lean_object* v___y_246_ = stack[4].m_obj;
lean_object* v_res_279_;
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_242_, v_i_243_, v_bs_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___boxed(lean_object* v_sz_280_, lean_object* v_i_281_, lean_object* v_bs_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
size_t v_sz_boxed_285_; size_t v_i_boxed_286_; lean_object* v_res_287_; 
v_sz_boxed_285_ = lean_unbox_usize(v_sz_280_);
lean_dec(v_sz_280_);
v_i_boxed_286_ = lean_unbox_usize(v_i_281_);
lean_dec(v_i_281_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_boxed_285_, v_i_boxed_286_, v_bs_282_, v___y_283_, v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object* v_ids_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; size_t v_sz_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_291_ = l_Lean_Syntax_getArgs(v_ids_288_);
v_sz_292_ = lean_array_size(v___x_291_);
v___x_293_ = ((size_t)0ULL);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_292_, v___x_293_, v___x_291_, v_a_289_, v_a_290_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object* v_ids_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_getBinderIds(v_ids_295_, v_a_296_, v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_ids_295_);
return v_res_298_;
}
}
static lean_object* _init_l_Lake_expandBinderIdent___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__0));
v___x_301_ = l_String_toRawSubstring_x27(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object* v_stx_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
lean_inc(v_stx_304_);
v___x_308_ = l_Lean_Syntax_isOfKind(v_stx_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_stx_304_);
lean_ctor_set(v___x_309_, 1, v_a_306_);
return v___x_309_;
}
else
{
lean_object* v_quotContext_310_; lean_object* v_currMacroScope_311_; lean_object* v_ref_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_stx_304_);
v_quotContext_310_ = lean_ctor_get(v_a_305_, 1);
v_currMacroScope_311_ = lean_ctor_get(v_a_305_, 2);
v_ref_312_ = lean_ctor_get(v_a_305_, 5);
v___x_313_ = 0;
v___x_314_ = l_Lean_SourceInfo_fromRef(v_ref_312_, v___x_313_);
v___x_315_ = lean_obj_once(&l_Lake_expandBinderIdent___closed__1, &l_Lake_expandBinderIdent___closed__1_once, _init_l_Lake_expandBinderIdent___closed__1);
v___x_316_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__2));
lean_inc(v_currMacroScope_311_);
lean_inc(v_quotContext_310_);
v___x_317_ = l_Lean_addMacroScope(v_quotContext_310_, v___x_316_, v_currMacroScope_311_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_319_, 0, v___x_314_);
lean_ctor_set(v___x_319_, 1, v___x_315_);
lean_ctor_set(v___x_319_, 2, v___x_317_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_306_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent___boxed(lean_object* v_stx_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lake_expandBinderIdent(v_stx_321_, v_a_322_, v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* v_stx_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Syntax_isNone(v_stx_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Lean_Syntax_getArg(v_stx_325_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = l_Lake_mkHoleFrom(v_stx_325_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* v_stx_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_expandOptIdent(v_stx_330_);
lean_dec(v_stx_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* v_ref_332_, lean_object* v_stx_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = l_Lean_Syntax_getNumArgs(v_stx_333_);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_dec_eq(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = l_Lean_Syntax_getArg(v_stx_333_, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l_Lake_mkHoleFrom(v_ref_332_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* v_ref_340_, lean_object* v_stx_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lake_expandBinderType(v_ref_340_, v_stx_341_);
lean_dec(v_stx_341_);
lean_dec(v_ref_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* v_optBinderModifier_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Syntax_getOptional_x3f(v_optBinderModifier_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
else
{
lean_object* v_val_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_val_346_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_val_346_);
lean_dec(v___x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_val_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* v_optBinderModifier_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_expandBinderModifier(v_optBinderModifier_354_);
lean_dec(v_optBinderModifier_354_);
return v_res_355_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(lean_object* v___x_356_, lean_object* v_stx_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
lean_inc(v___x_365_);
v___x_366_ = l_Lake_expandBinderIdent(v___x_365_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; size_t v___x_374_; size_t v___x_375_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
v_a_368_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_366_, 2);
v___x_369_ = l_Lake_expandBinderType(v___x_365_, v___x_356_);
v___x_370_ = 1;
v___x_371_ = lean_box(0);
lean_inc(v_stx_357_);
v___x_372_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_372_, 0, v_stx_357_);
lean_ctor_set(v___x_372_, 1, v_a_367_);
lean_ctor_set(v___x_372_, 2, v___x_369_);
lean_ctor_set(v___x_372_, 3, v___x_371_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*4, v___x_370_);
v___x_373_ = lean_array_push(v_b_361_, v___x_372_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_add(v_i_359_, v___x_374_);
v_i_359_ = v___x_375_;
v_b_361_ = v___x_373_;
v___y_363_ = v_a_368_;
goto _start;
}
else
{
lean_object* v_a_377_; lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec_ref(v_b_361_);
lean_dec(v_stx_357_);
v_a_377_ = lean_ctor_get(v___x_366_, 0);
v_a_378_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_366_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_inc(v_a_377_);
lean_dec(v___x_366_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_377_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v_stx_357_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_b_361_);
lean_ctor_set(v___x_386_, 1, v___y_363_);
return v___x_386_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_356_ = stack[0].m_obj;
lean_object* v_stx_357_ = stack[1].m_obj;
lean_object* v_as_358_ = stack[2].m_obj;
size_t v_i_359_ = stack[3].m_num;
size_t v_stop_360_ = stack[4].m_num;
lean_object* v_b_361_ = stack[5].m_obj;
lean_object* v___y_362_ = stack[6].m_obj;
lean_object* v___y_363_ = stack[7].m_obj;
lean_object* v_res_387_;
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_356_, v_stx_357_, v_as_358_, v_i_359_, v_stop_360_, v_b_361_, v___y_362_, v___y_363_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(lean_object* v___x_388_, lean_object* v_stx_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
size_t v_i_boxed_396_; size_t v_stop_boxed_397_; lean_object* v_res_398_; 
v_i_boxed_396_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_388_, v_stx_389_, v_as_390_, v_i_boxed_396_, v_stop_boxed_397_, v_b_393_, v___y_394_, v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_as_390_);
lean_dec(v___x_388_);
return v_res_398_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(lean_object* v___x_399_, lean_object* v_stx_400_, lean_object* v___x_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v_b_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
lean_inc(v___x_409_);
v___x_410_ = l_Lake_expandBinderIdent(v___x_409_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
v_a_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_410_, 2);
v___x_413_ = l_Lake_expandBinderType(v___x_409_, v___x_399_);
v___x_414_ = 0;
lean_inc(v___x_401_);
lean_inc(v_stx_400_);
v___x_415_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_415_, 0, v_stx_400_);
lean_ctor_set(v___x_415_, 1, v_a_411_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
lean_ctor_set(v___x_415_, 3, v___x_401_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*4, v___x_414_);
v___x_416_ = lean_array_push(v_b_405_, v___x_415_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_403_, v___x_417_);
v_i_403_ = v___x_418_;
v_b_405_ = v___x_416_;
v___y_407_ = v_a_412_;
goto _start;
}
else
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_b_405_);
lean_dec(v___x_401_);
lean_dec(v_stx_400_);
v_a_420_ = lean_ctor_get(v___x_410_, 0);
v_a_421_ = lean_ctor_get(v___x_410_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_410_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_inc(v_a_420_);
lean_dec(v___x_410_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v___x_429_; 
lean_dec(v___x_401_);
lean_dec(v_stx_400_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_b_405_);
lean_ctor_set(v___x_429_, 1, v___y_407_);
return v___x_429_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_399_ = stack[0].m_obj;
lean_object* v_stx_400_ = stack[1].m_obj;
lean_object* v___x_401_ = stack[2].m_obj;
lean_object* v_as_402_ = stack[3].m_obj;
size_t v_i_403_ = stack[4].m_num;
size_t v_stop_404_ = stack[5].m_num;
lean_object* v_b_405_ = stack[6].m_obj;
lean_object* v___y_406_ = stack[7].m_obj;
lean_object* v___y_407_ = stack[8].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_399_, v_stx_400_, v___x_401_, v_as_402_, v_i_403_, v_stop_404_, v_b_405_, v___y_406_, v___y_407_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(lean_object* v___x_431_, lean_object* v_stx_432_, lean_object* v___x_433_, lean_object* v_as_434_, lean_object* v_i_435_, lean_object* v_stop_436_, lean_object* v_b_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
size_t v_i_boxed_440_; size_t v_stop_boxed_441_; lean_object* v_res_442_; 
v_i_boxed_440_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_stop_boxed_441_ = lean_unbox_usize(v_stop_436_);
lean_dec(v_stop_436_);
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_431_, v_stx_432_, v___x_433_, v_as_434_, v_i_boxed_440_, v_stop_boxed_441_, v_b_437_, v___y_438_, v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec_ref(v_as_434_);
lean_dec(v___x_431_);
return v_res_442_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(lean_object* v___x_443_, lean_object* v_stx_444_, lean_object* v_as_445_, size_t v_i_446_, size_t v_stop_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_eq(v_i_446_, v_stop_447_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_array_uget_borrowed(v_as_445_, v_i_446_);
lean_inc(v___x_452_);
v___x_453_ = l_Lake_expandBinderIdent(v___x_452_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
v_a_455_ = lean_ctor_get(v___x_453_, 1);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_453_, 2);
v___x_456_ = l_Lake_expandBinderType(v___x_452_, v___x_443_);
v___x_457_ = 2;
v___x_458_ = lean_box(0);
lean_inc(v_stx_444_);
v___x_459_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_459_, 0, v_stx_444_);
lean_ctor_set(v___x_459_, 1, v_a_454_);
lean_ctor_set(v___x_459_, 2, v___x_456_);
lean_ctor_set(v___x_459_, 3, v___x_458_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*4, v___x_457_);
v___x_460_ = lean_array_push(v_b_448_, v___x_459_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_446_, v___x_461_);
v_i_446_ = v___x_462_;
v_b_448_ = v___x_460_;
v___y_450_ = v_a_455_;
goto _start;
}
else
{
lean_object* v_a_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_b_448_);
lean_dec(v_stx_444_);
v_a_464_ = lean_ctor_get(v___x_453_, 0);
v_a_465_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_453_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_inc(v_a_464_);
lean_dec(v___x_453_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_464_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_stx_444_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v_b_448_);
lean_ctor_set(v___x_473_, 1, v___y_450_);
return v___x_473_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_443_ = stack[0].m_obj;
lean_object* v_stx_444_ = stack[1].m_obj;
lean_object* v_as_445_ = stack[2].m_obj;
size_t v_i_446_ = stack[3].m_num;
size_t v_stop_447_ = stack[4].m_num;
lean_object* v_b_448_ = stack[5].m_obj;
lean_object* v___y_449_ = stack[6].m_obj;
lean_object* v___y_450_ = stack[7].m_obj;
lean_object* v_res_474_;
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_443_, v_stx_444_, v_as_445_, v_i_446_, v_stop_447_, v_b_448_, v___y_449_, v___y_450_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(lean_object* v___x_475_, lean_object* v_stx_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_stop_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
size_t v_i_boxed_483_; size_t v_stop_boxed_484_; lean_object* v_res_485_; 
v_i_boxed_483_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_stop_boxed_484_ = lean_unbox_usize(v_stop_479_);
lean_dec(v_stop_479_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_475_, v_stx_476_, v_as_477_, v_i_boxed_483_, v_stop_boxed_484_, v_b_480_, v___y_481_, v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v_as_477_);
lean_dec(v___x_475_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object* v_binders_510_, lean_object* v_stx_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_k_514_; uint8_t v___y_516_; uint8_t v___x_671_; 
lean_inc(v_stx_511_);
v_k_514_ = l_Lean_Syntax_getKind(v_stx_511_);
v___x_671_ = l_Lean_Syntax_isIdent(v_stx_511_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_673_ = lean_name_eq(v_k_514_, v___x_672_);
v___y_516_ = v___x_673_;
goto v___jp_515_;
}
else
{
v___y_516_ = v___x_671_;
goto v___jp_515_;
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_518_ = lean_name_eq(v_k_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_520_ = lean_name_eq(v_k_514_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_522_ = lean_name_eq(v_k_514_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_524_ = lean_name_eq(v_k_514_, v___x_523_);
lean_dec(v_k_514_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v_stx_511_);
lean_dec_ref(v_binders_510_);
v___x_525_ = l_Lean_Macro_throwUnsupported___redArg(v_a_513_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_id_528_; lean_object* v___x_529_; lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_526_);
v_id_528_ = l_Lake_expandOptIdent(v___x_527_);
lean_dec(v___x_527_);
v___x_529_ = l_Lake_expandBinderIdent(v_id_528_, v_a_512_, v_a_513_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_a_531_ = lean_ctor_get(v___x_529_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_544_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v_type_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_535_ = lean_unsigned_to_nat(2u);
v_type_536_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_535_);
v___x_537_ = 3;
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_539_, 0, v_stx_511_);
lean_ctor_set(v___x_539_, 1, v_a_530_);
lean_ctor_set(v___x_539_, 2, v_type_536_);
lean_ctor_set(v___x_539_, 3, v___x_538_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*4, v___x_537_);
v___x_540_ = lean_array_push(v_binders_510_, v___x_539_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_540_);
v___x_542_ = v___x_533_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_531_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v_k_514_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_545_);
v___x_547_ = l_Lake_getBinderIds(v___x_546_, v_a_512_, v_a_513_);
lean_dec(v___x_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_571_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_a_549_ = lean_ctor_get(v___x_547_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_571_ == 0)
{
v___x_551_ = v___x_547_;
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_array_get_size(v_a_548_);
v___x_555_ = lean_nat_dec_lt(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v_a_548_);
lean_dec(v_stx_511_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_binders_510_);
v___x_557_ = v___x_551_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_549_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(2u);
v___x_560_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_559_);
v___x_561_ = lean_nat_dec_le(v___x_554_, v___x_554_);
if (v___x_561_ == 0)
{
if (v___x_555_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_560_);
lean_dec(v_a_548_);
lean_dec(v_stx_511_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_binders_510_);
v___x_563_ = v___x_551_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_549_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
lean_del_object(v___x_551_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_554_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_560_, v_stx_511_, v_a_548_, v___x_565_, v___x_566_, v_binders_510_, v_a_512_, v_a_549_);
lean_dec(v_a_548_);
lean_dec(v___x_560_);
return v___x_567_;
}
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
lean_del_object(v___x_551_);
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_554_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_560_, v_stx_511_, v_a_548_, v___x_568_, v___x_569_, v_binders_510_, v_a_512_, v_a_549_);
lean_dec(v_a_548_);
lean_dec(v___x_560_);
return v___x_570_;
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_stx_511_);
lean_dec_ref(v_binders_510_);
v_a_572_ = lean_ctor_get(v___x_547_, 0);
v_a_573_ = lean_ctor_get(v___x_547_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_547_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_inc(v_a_572_);
lean_dec(v___x_547_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_572_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_k_514_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_581_);
v___x_583_ = l_Lake_getBinderIds(v___x_582_, v_a_512_, v_a_513_);
lean_dec(v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_607_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_a_585_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_607_ == 0)
{
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_607_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_607_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_array_get_size(v_a_584_);
v___x_591_ = lean_nat_dec_lt(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v_a_584_);
lean_dec(v_stx_511_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_binders_510_);
v___x_593_ = v___x_587_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_585_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_unsigned_to_nat(2u);
v___x_596_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_595_);
v___x_597_ = lean_nat_dec_le(v___x_590_, v___x_590_);
if (v___x_597_ == 0)
{
if (v___x_591_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v___x_596_);
lean_dec(v_a_584_);
lean_dec(v_stx_511_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_binders_510_);
v___x_599_ = v___x_587_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_585_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_587_);
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_590_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_596_, v_stx_511_, v_a_584_, v___x_601_, v___x_602_, v_binders_510_, v_a_512_, v_a_585_);
lean_dec(v_a_584_);
lean_dec(v___x_596_);
return v___x_603_;
}
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
lean_del_object(v___x_587_);
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_590_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_596_, v_stx_511_, v_a_584_, v___x_604_, v___x_605_, v_binders_510_, v_a_512_, v_a_585_);
lean_dec(v_a_584_);
lean_dec(v___x_596_);
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_stx_511_);
lean_dec_ref(v_binders_510_);
v_a_608_ = lean_ctor_get(v___x_583_, 0);
v_a_609_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_583_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_inc(v_a_608_);
lean_dec(v___x_583_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_k_514_);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_617_);
v___x_619_ = l_Lake_getBinderIds(v___x_618_, v_a_512_, v_a_513_);
lean_dec(v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_646_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_646_ == 0)
{
v___x_623_ = v___x_619_;
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_array_get_size(v_a_620_);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v_a_620_);
lean_dec(v_stx_511_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_binders_510_);
v___x_629_ = v___x_623_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_621_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_631_ = lean_unsigned_to_nat(2u);
v___x_632_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(3u);
v___x_634_ = l_Lean_Syntax_getArg(v_stx_511_, v___x_633_);
v___x_635_ = l_Lake_expandBinderModifier(v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = lean_nat_dec_le(v___x_626_, v___x_626_);
if (v___x_636_ == 0)
{
if (v___x_627_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v___x_635_);
lean_dec(v___x_632_);
lean_dec(v_a_620_);
lean_dec(v_stx_511_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_binders_510_);
v___x_638_ = v___x_623_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_a_621_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_623_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_626_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_632_, v_stx_511_, v___x_635_, v_a_620_, v___x_640_, v___x_641_, v_binders_510_, v_a_512_, v_a_621_);
lean_dec(v_a_620_);
lean_dec(v___x_632_);
return v___x_642_;
}
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
lean_del_object(v___x_623_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_626_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_632_, v_stx_511_, v___x_635_, v_a_620_, v___x_643_, v___x_644_, v_binders_510_, v_a_512_, v_a_621_);
lean_dec(v_a_620_);
lean_dec(v___x_632_);
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_stx_511_);
lean_dec_ref(v_binders_510_);
v_a_647_ = lean_ctor_get(v___x_619_, 0);
v_a_648_ = lean_ctor_get(v___x_619_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_619_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_inc(v_a_647_);
lean_dec(v___x_619_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_647_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_k_514_);
lean_inc(v_stx_511_);
v___x_656_ = l_Lake_expandBinderIdent(v_stx_511_, v_a_512_, v_a_513_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_a_658_ = lean_ctor_get(v___x_656_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_662_ = l_Lake_mkHoleFrom(v_stx_511_);
v___x_663_ = 0;
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_665_, 0, v_stx_511_);
lean_ctor_set(v___x_665_, 1, v_a_657_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
lean_ctor_set(v___x_665_, 3, v___x_664_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*4, v___x_663_);
v___x_666_ = lean_array_push(v_binders_510_, v___x_665_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_666_);
v___x_668_ = v___x_660_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_a_658_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore___boxed(lean_object* v_binders_674_, lean_object* v_stx_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lake_expandBinderCore(v_binders_674_, v_stx_675_, v_a_676_, v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object* v_stx_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_685_ = l_Lake_expandBinderCore(v___x_684_, v_stx_681_, v_a_682_, v_a_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder___boxed(lean_object* v_stx_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lake_expandBinder(v_stx_686_, v_a_687_, v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_689_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(lean_object* v_as_690_, size_t v_i_691_, size_t v_stop_692_, lean_object* v_b_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_eq(v_i_691_, v_stop_692_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_array_uget_borrowed(v_as_690_, v_i_691_);
lean_inc(v___x_697_);
v___x_698_ = l_Lake_expandBinderCore(v_b_693_, v___x_697_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v_a_700_; size_t v___x_701_; size_t v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
v_a_700_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_698_, 2);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_i_691_, v___x_701_);
v_i_691_ = v___x_702_;
v_b_693_ = v_a_699_;
v___y_695_ = v_a_700_;
goto _start;
}
else
{
return v___x_698_;
}
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_b_693_);
lean_ctor_set(v___x_704_, 1, v___y_695_);
return v___x_704_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_690_ = stack[0].m_obj;
size_t v_i_691_ = stack[1].m_num;
size_t v_stop_692_ = stack[2].m_num;
lean_object* v_b_693_ = stack[3].m_obj;
lean_object* v___y_694_ = stack[4].m_obj;
lean_object* v___y_695_ = stack[5].m_obj;
lean_object* v_res_705_;
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_690_, v_i_691_, v_stop_692_, v_b_693_, v___y_694_, v___y_695_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(lean_object* v_as_706_, lean_object* v_i_707_, lean_object* v_stop_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
size_t v_i_boxed_712_; size_t v_stop_boxed_713_; lean_object* v_res_714_; 
v_i_boxed_712_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_stop_boxed_713_ = lean_unbox_usize(v_stop_708_);
lean_dec(v_stop_708_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_706_, v_i_boxed_712_, v_stop_boxed_713_, v_b_709_, v___y_710_, v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_as_706_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* v_stxs_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_720_ = lean_array_get_size(v_stxs_715_);
v___x_721_ = lean_nat_dec_lt(v___x_718_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_719_);
lean_ctor_set(v___x_722_, 1, v_a_717_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_le(v___x_720_, v___x_720_);
if (v___x_723_ == 0)
{
if (v___x_721_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_719_);
lean_ctor_set(v___x_724_, 1, v_a_717_);
return v___x_724_;
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_720_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_715_, v___x_725_, v___x_726_, v___x_719_, v_a_716_, v_a_717_);
return v___x_727_;
}
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_720_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_715_, v___x_728_, v___x_729_, v___x_719_, v_a_716_, v_a_717_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* v_stxs_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_expandBinders(v_stxs_731_, v_a_732_, v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec_ref(v_stxs_731_);
return v_res_734_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__4(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Array_mkArray0___redArg();
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* v_x_750_){
_start:
{
uint8_t v_info_751_; 
v_info_751_ = lean_ctor_get_uint8(v_x_750_, sizeof(void*)*4);
switch(v_info_751_)
{
case 0:
{
lean_object* v_ref_752_; lean_object* v_id_753_; lean_object* v_type_754_; lean_object* v_modifier_x3f_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___y_768_; 
v_ref_752_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_ref_752_);
v_id_753_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_id_753_);
v_type_754_ = lean_ctor_get(v_x_750_, 2);
lean_inc(v_type_754_);
v_modifier_x3f_755_ = lean_ctor_get(v_x_750_, 3);
lean_inc(v_modifier_x3f_755_);
lean_dec_ref(v_x_750_);
v___x_756_ = 0;
v___x_757_ = l_Lean_SourceInfo_fromRef(v_ref_752_, v___x_756_);
lean_dec(v_ref_752_);
v___x_758_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_759_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_757_, 4);
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_762_ = l_Lean_Syntax_node1(v___x_757_, v___x_761_, v_id_753_);
v___x_763_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_757_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v___x_757_, v___x_761_, v___x_764_, v_type_754_);
v___x_766_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkBinder___closed__4, &l_Lake_BinderSyntaxView_mkBinder___closed__4_once, _init_l_Lake_BinderSyntaxView_mkBinder___closed__4);
if (lean_obj_tag(v_modifier_x3f_755_) == 1)
{
lean_object* v_val_774_; lean_object* v___x_775_; 
v_val_774_ = lean_ctor_get(v_modifier_x3f_755_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v_modifier_x3f_755_, 1);
v___x_775_ = l_Array_mkArray1___redArg(v_val_774_);
v___y_768_ = v___x_775_;
goto v___jp_767_;
}
else
{
lean_object* v___x_776_; 
lean_dec(v_modifier_x3f_755_);
v___x_776_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__6));
v___y_768_ = v___x_776_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_769_ = l_Array_append___redArg(v___x_766_, v___y_768_);
lean_dec_ref(v___y_768_);
lean_inc_n(v___x_757_, 2);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_757_);
lean_ctor_set(v___x_770_, 1, v___x_761_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_757_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_Syntax_node5(v___x_757_, v___x_758_, v___x_760_, v___x_762_, v___x_765_, v___x_770_, v___x_772_);
return v___x_773_;
}
}
case 1:
{
lean_object* v_ref_777_; lean_object* v_id_778_; lean_object* v_type_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_ref_777_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_ref_777_);
v_id_778_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_id_778_);
v_type_779_ = lean_ctor_get(v_x_750_, 2);
lean_inc(v_type_779_);
lean_dec_ref(v_x_750_);
v___x_780_ = 0;
v___x_781_ = l_Lean_SourceInfo_fromRef(v_ref_777_, v___x_780_);
lean_dec(v_ref_777_);
v___x_782_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_783_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_781_, 5);
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_781_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_786_ = l_Lean_Syntax_node1(v___x_781_, v___x_785_, v_id_778_);
v___x_787_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_781_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___x_781_, v___x_785_, v___x_788_, v_type_779_);
v___x_790_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_781_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_Syntax_node4(v___x_781_, v___x_782_, v___x_784_, v___x_786_, v___x_789_, v___x_791_);
return v___x_792_;
}
case 2:
{
lean_object* v_ref_793_; lean_object* v_id_794_; lean_object* v_type_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_ref_793_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_ref_793_);
v_id_794_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_id_794_);
v_type_795_ = lean_ctor_get(v_x_750_, 2);
lean_inc(v_type_795_);
lean_dec_ref(v_x_750_);
v___x_796_ = 0;
v___x_797_ = l_Lean_SourceInfo_fromRef(v_ref_793_, v___x_796_);
lean_dec(v_ref_793_);
v___x_798_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_799_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_797_, 5);
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_797_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_802_ = l_Lean_Syntax_node1(v___x_797_, v___x_801_, v_id_794_);
v___x_803_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_797_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_Syntax_node2(v___x_797_, v___x_801_, v___x_804_, v_type_795_);
v___x_806_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_797_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_Syntax_node4(v___x_797_, v___x_798_, v___x_800_, v___x_802_, v___x_805_, v___x_807_);
return v___x_808_;
}
default: 
{
lean_object* v_ref_809_; lean_object* v_id_810_; lean_object* v_type_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_ref_809_ = lean_ctor_get(v_x_750_, 0);
lean_inc(v_ref_809_);
v_id_810_ = lean_ctor_get(v_x_750_, 1);
lean_inc(v_id_810_);
v_type_811_ = lean_ctor_get(v_x_750_, 2);
lean_inc(v_type_811_);
lean_dec_ref(v_x_750_);
v___x_812_ = 0;
v___x_813_ = l_Lean_SourceInfo_fromRef(v_ref_809_, v___x_812_);
lean_dec(v_ref_809_);
v___x_814_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_815_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_813_, 4);
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_818_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_813_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_Syntax_node2(v___x_813_, v___x_817_, v_id_810_, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_813_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_Syntax_node4(v___x_813_, v___x_814_, v___x_816_, v___x_820_, v_type_811_, v___x_822_);
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object* v_res_831_, lean_object* v_self_832_){
_start:
{
lean_object* v_ref_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_ref_833_ = lean_ctor_get(v_self_832_, 0);
v___x_834_ = 0;
v___x_835_ = l_Lean_SourceInfo_fromRef(v_ref_833_, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__1));
v___x_837_ = l_Lake_BinderSyntaxView_mkBinder(v_self_832_);
v___x_838_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__2));
lean_inc(v___x_835_);
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_835_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Syntax_node3(v___x_835_, v___x_836_, v___x_837_, v___x_839_, v_res_831_);
return v___x_840_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(lean_object* v_as_841_, size_t v_i_842_, size_t v_stop_843_, lean_object* v_b_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_eq(v_i_842_, v_stop_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; size_t v___x_848_; size_t v___x_849_; 
v___x_846_ = lean_array_uget_borrowed(v_as_841_, v_i_842_);
lean_inc(v___x_846_);
v___x_847_ = l_Lake_BinderSyntaxView_mkDepArrow(v_b_844_, v___x_846_);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_add(v_i_842_, v___x_848_);
v_i_842_ = v___x_849_;
v_b_844_ = v___x_847_;
goto _start;
}
else
{
return v_b_844_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_841_ = stack[0].m_obj;
size_t v_i_842_ = stack[1].m_num;
size_t v_stop_843_ = stack[2].m_num;
lean_object* v_b_844_ = stack[3].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_841_, v_i_842_, v_stop_843_, v_b_844_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(lean_object* v_as_852_, lean_object* v_i_853_, lean_object* v_stop_854_, lean_object* v_b_855_){
_start:
{
size_t v_i_boxed_856_; size_t v_stop_boxed_857_; lean_object* v_res_858_; 
v_i_boxed_856_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_stop_boxed_857_ = lean_unbox_usize(v_stop_854_);
lean_dec(v_stop_854_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_852_, v_i_boxed_856_, v_stop_boxed_857_, v_b_855_);
lean_dec_ref(v_as_852_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object* v_binders_859_, lean_object* v_res_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_array_get_size(v_binders_859_);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
return v_res_860_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = lean_nat_dec_le(v___x_862_, v___x_862_);
if (v___x_864_ == 0)
{
if (v___x_863_ == 0)
{
return v_res_860_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_862_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_859_, v___x_865_, v___x_866_, v_res_860_);
return v___x_867_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((size_t)0ULL);
v___x_869_ = lean_usize_of_nat(v___x_862_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_859_, v___x_868_, v___x_869_, v_res_860_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object* v_binders_871_, lean_object* v_res_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lake_mkDepArrow(v_binders_871_, v_res_872_);
lean_dec_ref(v_binders_871_);
return v_res_873_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__8));
v___x_894_ = l_String_toRawSubstring_x27(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_895_ = l_Lean_firstFrontendMacroScope;
v___x_896_ = lean_box(0);
v___x_897_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__1));
v___x_898_ = l_Lean_addMacroScope(v___x_897_, v___x_896_, v___x_895_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object* v_x_924_){
_start:
{
lean_object* v_ref_925_; lean_object* v_id_926_; lean_object* v_type_927_; uint8_t v_info_928_; lean_object* v___x_929_; lean_object* v_ref_930_; 
v_ref_925_ = lean_ctor_get(v_x_924_, 0);
lean_inc(v_ref_925_);
v_id_926_ = lean_ctor_get(v_x_924_, 1);
lean_inc(v_id_926_);
v_type_927_ = lean_ctor_get(v_x_924_, 2);
lean_inc(v_type_927_);
v_info_928_ = lean_ctor_get_uint8(v_x_924_, sizeof(void*)*4);
lean_dec_ref(v_x_924_);
v___x_929_ = lean_box(0);
v_ref_930_ = l_Lean_replaceRef(v_ref_925_, v___x_929_);
lean_dec(v_ref_925_);
switch(v_info_928_)
{
case 0:
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_931_ = 0;
v___x_932_ = l_Lean_SourceInfo_fromRef(v_ref_930_, v___x_931_);
lean_dec(v_ref_930_);
v___x_933_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__3));
v___x_934_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__5));
v___x_935_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_932_, 7);
v___x_936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__7));
v___x_938_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__9, &l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9);
v___x_939_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__10, &l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10);
v___x_940_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__21));
v___x_941_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_941_, 0, v___x_932_);
lean_ctor_set(v___x_941_, 1, v___x_938_);
lean_ctor_set(v___x_941_, 2, v___x_939_);
lean_ctor_set(v___x_941_, 3, v___x_940_);
v___x_942_ = l_Lean_Syntax_node1(v___x_932_, v___x_937_, v___x_941_);
v___x_943_ = l_Lean_Syntax_node2(v___x_932_, v___x_934_, v___x_936_, v___x_942_);
v___x_944_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_932_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_947_ = l_Lean_Syntax_node1(v___x_932_, v___x_946_, v_type_927_);
v___x_948_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_932_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = l_Lean_Syntax_node5(v___x_932_, v___x_933_, v___x_943_, v_id_926_, v___x_945_, v___x_947_, v___x_949_);
return v___x_950_;
}
case 1:
{
uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_951_ = 0;
v___x_952_ = l_Lean_SourceInfo_fromRef(v_ref_930_, v___x_951_);
lean_dec(v_ref_930_);
v___x_953_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_954_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_952_, 5);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_957_ = l_Lean_Syntax_node1(v___x_952_, v___x_956_, v_id_926_);
v___x_958_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_952_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_Syntax_node2(v___x_952_, v___x_956_, v___x_959_, v_type_927_);
v___x_961_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_952_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_Syntax_node4(v___x_952_, v___x_953_, v___x_955_, v___x_957_, v___x_960_, v___x_962_);
return v___x_963_;
}
case 2:
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_964_ = 0;
v___x_965_ = l_Lean_SourceInfo_fromRef(v_ref_930_, v___x_964_);
lean_dec(v_ref_930_);
v___x_966_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_967_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_965_, 5);
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_970_ = l_Lean_Syntax_node1(v___x_965_, v___x_969_, v_id_926_);
v___x_971_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_965_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_Syntax_node2(v___x_965_, v___x_969_, v___x_972_, v_type_927_);
v___x_974_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_965_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_Syntax_node4(v___x_965_, v___x_966_, v___x_968_, v___x_970_, v___x_973_, v___x_975_);
return v___x_976_;
}
default: 
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_977_ = 0;
v___x_978_ = l_Lean_SourceInfo_fromRef(v_ref_930_, v___x_977_);
lean_dec(v_ref_930_);
v___x_979_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_980_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_978_, 4);
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_983_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_978_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_Syntax_node2(v___x_978_, v___x_982_, v_id_926_, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_978_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_Syntax_node4(v___x_978_, v___x_979_, v___x_981_, v___x_985_, v_type_927_, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* v_x_996_){
_start:
{
lean_object* v_ref_997_; lean_object* v_id_998_; lean_object* v___x_999_; lean_object* v_ref_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_ref_997_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_ref_997_);
v_id_998_ = lean_ctor_get(v_x_996_, 1);
lean_inc_n(v_id_998_, 2);
lean_dec_ref(v_x_996_);
v___x_999_ = lean_box(0);
v_ref_1000_ = l_Lean_replaceRef(v_ref_997_, v___x_999_);
lean_dec(v_ref_997_);
v___x_1001_ = 0;
v___x_1002_ = l_Lean_SourceInfo_fromRef(v_ref_1000_, v___x_1001_);
lean_dec(v_ref_1000_);
v___x_1003_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__1));
v___x_1004_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_1002_, 3);
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__2));
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1002_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1002_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node5(v___x_1002_, v___x_1003_, v___x_1005_, v_id_998_, v___x_1007_, v_id_998_, v___x_1009_);
return v___x_1010_;
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
