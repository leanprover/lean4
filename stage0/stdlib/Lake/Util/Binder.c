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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_dec_ref(v_x_96_);
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
lean_object* v_v_247_; lean_object* v___x_248_; lean_object* v_bs_x27_249_; lean_object* v_a_251_; lean_object* v_a_252_; uint8_t v___y_258_; lean_object* v_k_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_v_247_ = lean_array_uget(v_bs_242_, v_i_241_);
v___x_248_ = lean_unsigned_to_nat(0u);
v_bs_x27_249_ = lean_array_uset(v_bs_242_, v_i_241_, v___x_248_);
lean_inc(v_v_247_);
v_k_272_ = l_Lean_Syntax_getKind(v_v_247_);
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__2));
v___x_274_ = lean_name_eq(v_k_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_276_ = lean_name_eq(v_k_272_, v___x_275_);
lean_dec(v_k_272_);
v___y_258_ = v___x_276_;
goto v___jp_257_;
}
else
{
lean_dec(v_k_272_);
v___y_258_ = v___x_274_;
goto v___jp_257_;
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
v___jp_257_:
{
if (v___y_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___closed__0));
v___x_260_ = l_Lean_Macro_throwErrorAt___redArg(v_v_247_, v___x_259_, v___y_243_, v___y_244_);
lean_dec(v_v_247_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v_a_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
v_a_262_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_a_262_);
lean_dec_ref(v___x_260_);
v_a_251_ = v_a_261_;
v_a_252_ = v_a_262_;
goto v___jp_250_;
}
else
{
lean_object* v_a_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_bs_x27_249_);
v_a_263_ = lean_ctor_get(v___x_260_, 0);
v_a_264_ = lean_ctor_get(v___x_260_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_260_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_inc(v_a_263_);
lean_dec(v___x_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_263_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0___boxed(lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_bs_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_283_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_boxed_282_, v_i_boxed_283_, v_bs_279_, v___y_280_, v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object* v_ids_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_288_ = l_Lean_Syntax_getArgs(v_ids_285_);
v_sz_289_ = lean_array_size(v___x_288_);
v___x_290_ = ((size_t)0ULL);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_getBinderIds_spec__0(v_sz_289_, v___x_290_, v___x_288_, v_a_286_, v_a_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object* v_ids_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_getBinderIds(v_ids_292_, v_a_293_, v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_ids_292_);
return v_res_295_;
}
}
static lean_object* _init_l_Lake_expandBinderIdent___closed__1(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__0));
v___x_298_ = l_String_toRawSubstring_x27(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object* v_stx_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
lean_inc(v_stx_301_);
v___x_305_ = l_Lean_Syntax_isOfKind(v_stx_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_stx_301_);
lean_ctor_set(v___x_306_, 1, v_a_303_);
return v___x_306_;
}
else
{
lean_object* v_quotContext_307_; lean_object* v_currMacroScope_308_; lean_object* v_ref_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_stx_301_);
v_quotContext_307_ = lean_ctor_get(v_a_302_, 1);
v_currMacroScope_308_ = lean_ctor_get(v_a_302_, 2);
v_ref_309_ = lean_ctor_get(v_a_302_, 5);
v___x_310_ = 0;
v___x_311_ = l_Lean_SourceInfo_fromRef(v_ref_309_, v___x_310_);
v___x_312_ = lean_obj_once(&l_Lake_expandBinderIdent___closed__1, &l_Lake_expandBinderIdent___closed__1_once, _init_l_Lake_expandBinderIdent___closed__1);
v___x_313_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__2));
lean_inc(v_currMacroScope_308_);
lean_inc(v_quotContext_307_);
v___x_314_ = l_Lean_addMacroScope(v_quotContext_307_, v___x_313_, v_currMacroScope_308_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_316_, 0, v___x_311_);
lean_ctor_set(v___x_316_, 1, v___x_312_);
lean_ctor_set(v___x_316_, 2, v___x_314_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_303_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent___boxed(lean_object* v_stx_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lake_expandBinderIdent(v_stx_318_, v_a_319_, v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* v_stx_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Syntax_isNone(v_stx_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Lean_Syntax_getArg(v_stx_322_, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = l_Lake_mkHoleFrom(v_stx_322_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* v_stx_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lake_expandOptIdent(v_stx_327_);
lean_dec(v_stx_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* v_ref_329_, lean_object* v_stx_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_Syntax_getNumArgs(v_stx_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_dec_eq(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_334_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = l_Lake_mkHoleFrom(v_ref_329_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* v_ref_337_, lean_object* v_stx_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lake_expandBinderType(v_ref_337_, v_stx_338_);
lean_dec(v_stx_338_);
lean_dec(v_ref_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* v_optBinderModifier_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Syntax_getOptional_x3f(v_optBinderModifier_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(0);
return v___x_342_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_val_343_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_val_343_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_val_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* v_optBinderModifier_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lake_expandBinderModifier(v_optBinderModifier_351_);
lean_dec(v_optBinderModifier_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(lean_object* v___x_353_, lean_object* v_stx_354_, lean_object* v_as_355_, size_t v_i_356_, size_t v_stop_357_, lean_object* v_b_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_eq(v_i_356_, v_stop_357_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_array_uget_borrowed(v_as_355_, v_i_356_);
lean_inc(v___x_362_);
v___x_363_ = l_Lake_expandBinderIdent(v___x_362_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_a_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
v_a_365_ = lean_ctor_get(v___x_363_, 1);
lean_inc(v_a_365_);
lean_dec_ref(v___x_363_);
v___x_366_ = l_Lake_expandBinderType(v___x_362_, v___x_353_);
v___x_367_ = 1;
v___x_368_ = lean_box(0);
lean_inc(v_stx_354_);
v___x_369_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_369_, 0, v_stx_354_);
lean_ctor_set(v___x_369_, 1, v_a_364_);
lean_ctor_set(v___x_369_, 2, v___x_366_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*4, v___x_367_);
v___x_370_ = lean_array_push(v_b_358_, v___x_369_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_356_, v___x_371_);
v_i_356_ = v___x_372_;
v_b_358_ = v___x_370_;
v___y_360_ = v_a_365_;
goto _start;
}
else
{
lean_object* v_a_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_b_358_);
lean_dec(v_stx_354_);
v_a_374_ = lean_ctor_get(v___x_363_, 0);
v_a_375_ = lean_ctor_get(v___x_363_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_363_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_inc(v_a_374_);
lean_dec(v___x_363_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec(v_stx_354_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_b_358_);
lean_ctor_set(v___x_383_, 1, v___y_360_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(lean_object* v___x_384_, lean_object* v_stx_385_, lean_object* v_as_386_, lean_object* v_i_387_, lean_object* v_stop_388_, lean_object* v_b_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_i_boxed_392_; size_t v_stop_boxed_393_; lean_object* v_res_394_; 
v_i_boxed_392_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_stop_boxed_393_ = lean_unbox_usize(v_stop_388_);
lean_dec(v_stop_388_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_384_, v_stx_385_, v_as_386_, v_i_boxed_392_, v_stop_boxed_393_, v_b_389_, v___y_390_, v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec_ref(v_as_386_);
lean_dec(v___x_384_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(lean_object* v___x_395_, lean_object* v_stx_396_, lean_object* v___x_397_, lean_object* v_as_398_, size_t v_i_399_, size_t v_stop_400_, lean_object* v_b_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_eq(v_i_399_, v_stop_400_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_array_uget_borrowed(v_as_398_, v_i_399_);
lean_inc(v___x_405_);
v___x_406_ = l_Lake_expandBinderIdent(v___x_405_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
v_a_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_a_408_);
lean_dec_ref(v___x_406_);
v___x_409_ = l_Lake_expandBinderType(v___x_405_, v___x_395_);
v___x_410_ = 0;
lean_inc(v___x_397_);
lean_inc(v_stx_396_);
v___x_411_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_411_, 0, v_stx_396_);
lean_ctor_set(v___x_411_, 1, v_a_407_);
lean_ctor_set(v___x_411_, 2, v___x_409_);
lean_ctor_set(v___x_411_, 3, v___x_397_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*4, v___x_410_);
v___x_412_ = lean_array_push(v_b_401_, v___x_411_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_399_, v___x_413_);
v_i_399_ = v___x_414_;
v_b_401_ = v___x_412_;
v___y_403_ = v_a_408_;
goto _start;
}
else
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_b_401_);
lean_dec(v___x_397_);
lean_dec(v_stx_396_);
v_a_416_ = lean_ctor_get(v___x_406_, 0);
v_a_417_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_406_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_inc(v_a_416_);
lean_dec(v___x_406_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_416_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v___x_425_; 
lean_dec(v___x_397_);
lean_dec(v_stx_396_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_b_401_);
lean_ctor_set(v___x_425_, 1, v___y_403_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(lean_object* v___x_426_, lean_object* v_stx_427_, lean_object* v___x_428_, lean_object* v_as_429_, lean_object* v_i_430_, lean_object* v_stop_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
size_t v_i_boxed_435_; size_t v_stop_boxed_436_; lean_object* v_res_437_; 
v_i_boxed_435_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_stop_boxed_436_ = lean_unbox_usize(v_stop_431_);
lean_dec(v_stop_431_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_426_, v_stx_427_, v___x_428_, v_as_429_, v_i_boxed_435_, v_stop_boxed_436_, v_b_432_, v___y_433_, v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v_as_429_);
lean_dec(v___x_426_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(lean_object* v___x_438_, lean_object* v_stx_439_, lean_object* v_as_440_, size_t v_i_441_, size_t v_stop_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_441_, v_stop_442_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_array_uget_borrowed(v_as_440_, v_i_441_);
lean_inc(v___x_447_);
v___x_448_ = l_Lake_expandBinderIdent(v___x_447_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v_a_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; size_t v___x_456_; size_t v___x_457_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
v_a_450_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_a_450_);
lean_dec_ref(v___x_448_);
v___x_451_ = l_Lake_expandBinderType(v___x_447_, v___x_438_);
v___x_452_ = 2;
v___x_453_ = lean_box(0);
lean_inc(v_stx_439_);
v___x_454_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_454_, 0, v_stx_439_);
lean_ctor_set(v___x_454_, 1, v_a_449_);
lean_ctor_set(v___x_454_, 2, v___x_451_);
lean_ctor_set(v___x_454_, 3, v___x_453_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*4, v___x_452_);
v___x_455_ = lean_array_push(v_b_443_, v___x_454_);
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_441_, v___x_456_);
v_i_441_ = v___x_457_;
v_b_443_ = v___x_455_;
v___y_445_ = v_a_450_;
goto _start;
}
else
{
lean_object* v_a_459_; lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_b_443_);
lean_dec(v_stx_439_);
v_a_459_ = lean_ctor_get(v___x_448_, 0);
v_a_460_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_448_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_inc(v_a_459_);
lean_dec(v___x_448_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_stx_439_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_b_443_);
lean_ctor_set(v___x_468_, 1, v___y_445_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(lean_object* v___x_469_, lean_object* v_stx_470_, lean_object* v_as_471_, lean_object* v_i_472_, lean_object* v_stop_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
size_t v_i_boxed_477_; size_t v_stop_boxed_478_; lean_object* v_res_479_; 
v_i_boxed_477_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_stop_boxed_478_ = lean_unbox_usize(v_stop_473_);
lean_dec(v_stop_473_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_469_, v_stx_470_, v_as_471_, v_i_boxed_477_, v_stop_boxed_478_, v_b_474_, v___y_475_, v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec_ref(v_as_471_);
lean_dec(v___x_469_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object* v_binders_504_, lean_object* v_stx_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_k_508_; uint8_t v___y_510_; uint8_t v___x_665_; 
lean_inc(v_stx_505_);
v_k_508_ = l_Lean_Syntax_getKind(v_stx_505_);
v___x_665_ = l_Lean_Syntax_isIdent(v_stx_505_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_667_ = lean_name_eq(v_k_508_, v___x_666_);
v___y_510_ = v___x_667_;
goto v___jp_509_;
}
else
{
v___y_510_ = v___x_665_;
goto v___jp_509_;
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_512_ = lean_name_eq(v_k_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_514_ = lean_name_eq(v_k_508_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_516_ = lean_name_eq(v_k_508_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_518_ = lean_name_eq(v_k_508_, v___x_517_);
lean_dec(v_k_508_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v_stx_505_);
lean_dec_ref(v_binders_504_);
v___x_519_ = l_Lean_Macro_throwUnsupported___redArg(v_a_507_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_id_522_; lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_538_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_520_);
v_id_522_ = l_Lake_expandOptIdent(v___x_521_);
lean_dec(v___x_521_);
v___x_523_ = l_Lake_expandBinderIdent(v_id_522_, v_a_506_, v_a_507_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_a_525_ = lean_ctor_get(v___x_523_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_538_ == 0)
{
v___x_527_ = v___x_523_;
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v_type_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_529_ = lean_unsigned_to_nat(2u);
v_type_530_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_529_);
v___x_531_ = 3;
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_533_, 0, v_stx_505_);
lean_ctor_set(v___x_533_, 1, v_a_524_);
lean_ctor_set(v___x_533_, 2, v_type_530_);
lean_ctor_set(v___x_533_, 3, v___x_532_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*4, v___x_531_);
v___x_534_ = lean_array_push(v_binders_504_, v___x_533_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_534_);
v___x_536_ = v___x_527_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_a_525_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_k_508_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_539_);
v___x_541_ = l_Lake_getBinderIds(v___x_540_, v_a_506_, v_a_507_);
lean_dec(v___x_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_565_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_a_543_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_565_ == 0)
{
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_a_542_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v_a_542_);
lean_dec(v_stx_505_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_binders_504_);
v___x_551_ = v___x_545_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_a_543_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_553_);
v___x_555_ = lean_nat_dec_le(v___x_548_, v___x_548_);
if (v___x_555_ == 0)
{
if (v___x_549_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v___x_554_);
lean_dec(v_a_542_);
lean_dec(v_stx_505_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_binders_504_);
v___x_557_ = v___x_545_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_543_);
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
size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
lean_del_object(v___x_545_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_548_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_554_, v_stx_505_, v_a_542_, v___x_559_, v___x_560_, v_binders_504_, v_a_506_, v_a_543_);
lean_dec(v_a_542_);
lean_dec(v___x_554_);
return v___x_561_;
}
}
else
{
size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_545_);
v___x_562_ = ((size_t)0ULL);
v___x_563_ = lean_usize_of_nat(v___x_548_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_554_, v_stx_505_, v_a_542_, v___x_562_, v___x_563_, v_binders_504_, v_a_506_, v_a_543_);
lean_dec(v_a_542_);
lean_dec(v___x_554_);
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_stx_505_);
lean_dec_ref(v_binders_504_);
v_a_566_ = lean_ctor_get(v___x_541_, 0);
v_a_567_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_541_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_inc(v_a_566_);
lean_dec(v___x_541_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_k_508_);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_575_);
v___x_577_ = l_Lake_getBinderIds(v___x_576_, v_a_506_, v_a_507_);
lean_dec(v___x_576_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_601_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_a_579_ = lean_ctor_get(v___x_577_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_601_ == 0)
{
v___x_581_ = v___x_577_;
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_array_get_size(v_a_578_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v_a_578_);
lean_dec(v_stx_505_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_binders_504_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_a_579_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(2u);
v___x_590_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_589_);
v___x_591_ = lean_nat_dec_le(v___x_584_, v___x_584_);
if (v___x_591_ == 0)
{
if (v___x_585_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v___x_590_);
lean_dec(v_a_578_);
lean_dec(v_stx_505_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_binders_504_);
v___x_593_ = v___x_581_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_579_);
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
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_581_);
v___x_595_ = ((size_t)0ULL);
v___x_596_ = lean_usize_of_nat(v___x_584_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_590_, v_stx_505_, v_a_578_, v___x_595_, v___x_596_, v_binders_504_, v_a_506_, v_a_579_);
lean_dec(v_a_578_);
lean_dec(v___x_590_);
return v___x_597_;
}
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_581_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = lean_usize_of_nat(v___x_584_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_590_, v_stx_505_, v_a_578_, v___x_598_, v___x_599_, v_binders_504_, v_a_506_, v_a_579_);
lean_dec(v_a_578_);
lean_dec(v___x_590_);
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_stx_505_);
lean_dec_ref(v_binders_504_);
v_a_602_ = lean_ctor_get(v___x_577_, 0);
v_a_603_ = lean_ctor_get(v___x_577_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_577_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_inc(v_a_602_);
lean_dec(v___x_577_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_k_508_);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_611_);
v___x_613_ = l_Lake_getBinderIds(v___x_612_, v_a_506_, v_a_507_);
lean_dec(v___x_612_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_640_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_a_615_ = lean_ctor_get(v___x_613_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_640_ == 0)
{
v___x_617_ = v___x_613_;
v_isShared_618_ = v_isSharedCheck_640_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_640_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v_a_614_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v_a_614_);
lean_dec(v_stx_505_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_binders_504_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_a_615_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(3u);
v___x_628_ = l_Lean_Syntax_getArg(v_stx_505_, v___x_627_);
v___x_629_ = l_Lake_expandBinderModifier(v___x_628_);
lean_dec(v___x_628_);
v___x_630_ = lean_nat_dec_le(v___x_620_, v___x_620_);
if (v___x_630_ == 0)
{
if (v___x_621_ == 0)
{
lean_object* v___x_632_; 
lean_dec(v___x_629_);
lean_dec(v___x_626_);
lean_dec(v_a_614_);
lean_dec(v_stx_505_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_binders_504_);
v___x_632_ = v___x_617_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_binders_504_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_615_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
lean_del_object(v___x_617_);
v___x_634_ = ((size_t)0ULL);
v___x_635_ = lean_usize_of_nat(v___x_620_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_626_, v_stx_505_, v___x_629_, v_a_614_, v___x_634_, v___x_635_, v_binders_504_, v_a_506_, v_a_615_);
lean_dec(v_a_614_);
lean_dec(v___x_626_);
return v___x_636_;
}
}
else
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
lean_del_object(v___x_617_);
v___x_637_ = ((size_t)0ULL);
v___x_638_ = lean_usize_of_nat(v___x_620_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_626_, v_stx_505_, v___x_629_, v_a_614_, v___x_637_, v___x_638_, v_binders_504_, v_a_506_, v_a_615_);
lean_dec(v_a_614_);
lean_dec(v___x_626_);
return v___x_639_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_stx_505_);
lean_dec_ref(v_binders_504_);
v_a_641_ = lean_ctor_get(v___x_613_, 0);
v_a_642_ = lean_ctor_get(v___x_613_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_613_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_inc(v_a_641_);
lean_dec(v___x_613_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_641_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_k_508_);
lean_inc(v_stx_505_);
v___x_650_ = l_Lake_expandBinderIdent(v_stx_505_, v_a_506_, v_a_507_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_a_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_664_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_656_ = l_Lake_mkHoleFrom(v_stx_505_);
v___x_657_ = 0;
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_659_, 0, v_stx_505_);
lean_ctor_set(v___x_659_, 1, v_a_651_);
lean_ctor_set(v___x_659_, 2, v___x_656_);
lean_ctor_set(v___x_659_, 3, v___x_658_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*4, v___x_657_);
v___x_660_ = lean_array_push(v_binders_504_, v___x_659_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_660_);
v___x_662_ = v___x_654_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_652_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore___boxed(lean_object* v_binders_668_, lean_object* v_stx_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lake_expandBinderCore(v_binders_668_, v_stx_669_, v_a_670_, v_a_671_);
lean_dec_ref(v_a_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object* v_stx_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_679_ = l_Lake_expandBinderCore(v___x_678_, v_stx_675_, v_a_676_, v_a_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder___boxed(lean_object* v_stx_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lake_expandBinder(v_stx_680_, v_a_681_, v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(lean_object* v_as_684_, size_t v_i_685_, size_t v_stop_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_usize_dec_eq(v_i_685_, v_stop_686_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_array_uget_borrowed(v_as_684_, v_i_685_);
lean_inc(v___x_691_);
v___x_692_ = l_Lake_expandBinderCore(v_b_687_, v___x_691_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_a_694_; size_t v___x_695_; size_t v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
v_a_694_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_a_694_);
lean_dec_ref(v___x_692_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_685_, v___x_695_);
v_i_685_ = v___x_696_;
v_b_687_ = v_a_693_;
v___y_689_ = v_a_694_;
goto _start;
}
else
{
return v___x_692_;
}
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_b_687_);
lean_ctor_set(v___x_698_, 1, v___y_689_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(lean_object* v_as_699_, lean_object* v_i_700_, lean_object* v_stop_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
size_t v_i_boxed_705_; size_t v_stop_boxed_706_; lean_object* v_res_707_; 
v_i_boxed_705_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_stop_boxed_706_ = lean_unbox_usize(v_stop_701_);
lean_dec(v_stop_701_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_699_, v_i_boxed_705_, v_stop_boxed_706_, v_b_702_, v___y_703_, v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec_ref(v_as_699_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* v_stxs_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_713_ = lean_array_get_size(v_stxs_708_);
v___x_714_ = lean_nat_dec_lt(v___x_711_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v_a_710_);
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = lean_nat_dec_le(v___x_713_, v___x_713_);
if (v___x_716_ == 0)
{
if (v___x_714_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_712_);
lean_ctor_set(v___x_717_, 1, v_a_710_);
return v___x_717_;
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_713_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_708_, v___x_718_, v___x_719_, v___x_712_, v_a_709_, v_a_710_);
return v___x_720_;
}
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)0ULL);
v___x_722_ = lean_usize_of_nat(v___x_713_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_708_, v___x_721_, v___x_722_, v___x_712_, v_a_709_, v_a_710_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* v_stxs_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lake_expandBinders(v_stxs_724_, v_a_725_, v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec_ref(v_stxs_724_);
return v_res_727_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__4(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Array_mkArray0(lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* v_x_743_){
_start:
{
uint8_t v_info_744_; 
v_info_744_ = lean_ctor_get_uint8(v_x_743_, sizeof(void*)*4);
switch(v_info_744_)
{
case 0:
{
lean_object* v_ref_745_; lean_object* v_id_746_; lean_object* v_type_747_; lean_object* v_modifier_x3f_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___y_761_; 
v_ref_745_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_ref_745_);
v_id_746_ = lean_ctor_get(v_x_743_, 1);
lean_inc(v_id_746_);
v_type_747_ = lean_ctor_get(v_x_743_, 2);
lean_inc(v_type_747_);
v_modifier_x3f_748_ = lean_ctor_get(v_x_743_, 3);
lean_inc(v_modifier_x3f_748_);
lean_dec_ref(v_x_743_);
v___x_749_ = 0;
v___x_750_ = l_Lean_SourceInfo_fromRef(v_ref_745_, v___x_749_);
lean_dec(v_ref_745_);
v___x_751_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_752_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_750_, 4);
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_755_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v_id_746_);
v___x_756_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_750_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Syntax_node2(v___x_750_, v___x_754_, v___x_757_, v_type_747_);
v___x_759_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkBinder___closed__4, &l_Lake_BinderSyntaxView_mkBinder___closed__4_once, _init_l_Lake_BinderSyntaxView_mkBinder___closed__4);
if (lean_obj_tag(v_modifier_x3f_748_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v_modifier_x3f_748_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v_modifier_x3f_748_);
v___x_768_ = l_Array_mkArray1___redArg(v_val_767_);
v___y_761_ = v___x_768_;
goto v___jp_760_;
}
else
{
lean_object* v___x_769_; 
lean_dec(v_modifier_x3f_748_);
v___x_769_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__6));
v___y_761_ = v___x_769_;
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_762_ = l_Array_append___redArg(v___x_759_, v___y_761_);
lean_dec_ref(v___y_761_);
lean_inc_n(v___x_750_, 2);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_750_);
lean_ctor_set(v___x_763_, 1, v___x_754_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_750_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_Syntax_node5(v___x_750_, v___x_751_, v___x_753_, v___x_755_, v___x_758_, v___x_763_, v___x_765_);
return v___x_766_;
}
}
case 1:
{
lean_object* v_ref_770_; lean_object* v_id_771_; lean_object* v_type_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ref_770_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_ref_770_);
v_id_771_ = lean_ctor_get(v_x_743_, 1);
lean_inc(v_id_771_);
v_type_772_ = lean_ctor_get(v_x_743_, 2);
lean_inc(v_type_772_);
lean_dec_ref(v_x_743_);
v___x_773_ = 0;
v___x_774_ = l_Lean_SourceInfo_fromRef(v_ref_770_, v___x_773_);
lean_dec(v_ref_770_);
v___x_775_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_776_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_774_, 5);
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_779_ = l_Lean_Syntax_node1(v___x_774_, v___x_778_, v_id_771_);
v___x_780_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_774_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Syntax_node2(v___x_774_, v___x_778_, v___x_781_, v_type_772_);
v___x_783_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_774_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_Syntax_node4(v___x_774_, v___x_775_, v___x_777_, v___x_779_, v___x_782_, v___x_784_);
return v___x_785_;
}
case 2:
{
lean_object* v_ref_786_; lean_object* v_id_787_; lean_object* v_type_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_ref_786_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_ref_786_);
v_id_787_ = lean_ctor_get(v_x_743_, 1);
lean_inc(v_id_787_);
v_type_788_ = lean_ctor_get(v_x_743_, 2);
lean_inc(v_type_788_);
lean_dec_ref(v_x_743_);
v___x_789_ = 0;
v___x_790_ = l_Lean_SourceInfo_fromRef(v_ref_786_, v___x_789_);
lean_dec(v_ref_786_);
v___x_791_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_792_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_790_, 5);
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_790_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_795_ = l_Lean_Syntax_node1(v___x_790_, v___x_794_, v_id_787_);
v___x_796_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_790_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v___x_790_, v___x_794_, v___x_797_, v_type_788_);
v___x_799_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_790_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_Syntax_node4(v___x_790_, v___x_791_, v___x_793_, v___x_795_, v___x_798_, v___x_800_);
return v___x_801_;
}
default: 
{
lean_object* v_ref_802_; lean_object* v_id_803_; lean_object* v_type_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_ref_802_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_ref_802_);
v_id_803_ = lean_ctor_get(v_x_743_, 1);
lean_inc(v_id_803_);
v_type_804_ = lean_ctor_get(v_x_743_, 2);
lean_inc(v_type_804_);
lean_dec_ref(v_x_743_);
v___x_805_ = 0;
v___x_806_ = l_Lean_SourceInfo_fromRef(v_ref_802_, v___x_805_);
lean_dec(v_ref_802_);
v___x_807_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_808_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_806_, 4);
v___x_809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_811_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_806_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_Syntax_node2(v___x_806_, v___x_810_, v_id_803_, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_806_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_Syntax_node4(v___x_806_, v___x_807_, v___x_809_, v___x_813_, v_type_804_, v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object* v_res_824_, lean_object* v_self_825_){
_start:
{
lean_object* v_ref_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ref_826_ = lean_ctor_get(v_self_825_, 0);
v___x_827_ = 0;
v___x_828_ = l_Lean_SourceInfo_fromRef(v_ref_826_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__1));
v___x_830_ = l_Lake_BinderSyntaxView_mkBinder(v_self_825_);
v___x_831_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__2));
lean_inc(v___x_828_);
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_828_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Syntax_node3(v___x_828_, v___x_829_, v___x_830_, v___x_832_, v_res_824_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(lean_object* v_as_834_, size_t v_i_835_, size_t v_stop_836_, lean_object* v_b_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_eq(v_i_835_, v_stop_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; size_t v___x_841_; size_t v___x_842_; 
v___x_839_ = lean_array_uget_borrowed(v_as_834_, v_i_835_);
lean_inc(v___x_839_);
v___x_840_ = l_Lake_BinderSyntaxView_mkDepArrow(v_b_837_, v___x_839_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_835_, v___x_841_);
v_i_835_ = v___x_842_;
v_b_837_ = v___x_840_;
goto _start;
}
else
{
return v_b_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(lean_object* v_as_844_, lean_object* v_i_845_, lean_object* v_stop_846_, lean_object* v_b_847_){
_start:
{
size_t v_i_boxed_848_; size_t v_stop_boxed_849_; lean_object* v_res_850_; 
v_i_boxed_848_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_stop_boxed_849_ = lean_unbox_usize(v_stop_846_);
lean_dec(v_stop_846_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_844_, v_i_boxed_848_, v_stop_boxed_849_, v_b_847_);
lean_dec_ref(v_as_844_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object* v_binders_851_, lean_object* v_res_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_array_get_size(v_binders_851_);
v___x_855_ = lean_nat_dec_lt(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
return v_res_852_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = lean_nat_dec_le(v___x_854_, v___x_854_);
if (v___x_856_ == 0)
{
if (v___x_855_ == 0)
{
return v_res_852_;
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_854_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_851_, v___x_857_, v___x_858_, v_res_852_);
return v___x_859_;
}
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_854_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_851_, v___x_860_, v___x_861_, v_res_852_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object* v_binders_863_, lean_object* v_res_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lake_mkDepArrow(v_binders_863_, v_res_864_);
lean_dec_ref(v_binders_863_);
return v_res_865_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__8));
v___x_886_ = l_String_toRawSubstring_x27(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_firstFrontendMacroScope;
v___x_888_ = lean_box(0);
v___x_889_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__1));
v___x_890_ = l_Lean_addMacroScope(v___x_889_, v___x_888_, v___x_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object* v_x_916_){
_start:
{
lean_object* v_ref_917_; lean_object* v_id_918_; lean_object* v_type_919_; uint8_t v_info_920_; lean_object* v___x_921_; lean_object* v_ref_922_; 
v_ref_917_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_ref_917_);
v_id_918_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_id_918_);
v_type_919_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_type_919_);
v_info_920_ = lean_ctor_get_uint8(v_x_916_, sizeof(void*)*4);
lean_dec_ref(v_x_916_);
v___x_921_ = lean_box(0);
v_ref_922_ = l_Lean_replaceRef(v_ref_917_, v___x_921_);
lean_dec(v_ref_917_);
switch(v_info_920_)
{
case 0:
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_923_ = 0;
v___x_924_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_923_);
lean_dec(v_ref_922_);
v___x_925_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__3));
v___x_926_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__5));
v___x_927_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_924_, 7);
v___x_928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_924_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__7));
v___x_930_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__9, &l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9);
v___x_931_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__10, &l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10);
v___x_932_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__21));
v___x_933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_933_, 0, v___x_924_);
lean_ctor_set(v___x_933_, 1, v___x_930_);
lean_ctor_set(v___x_933_, 2, v___x_931_);
lean_ctor_set(v___x_933_, 3, v___x_932_);
v___x_934_ = l_Lean_Syntax_node1(v___x_924_, v___x_929_, v___x_933_);
v___x_935_ = l_Lean_Syntax_node2(v___x_924_, v___x_926_, v___x_928_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_924_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_939_ = l_Lean_Syntax_node1(v___x_924_, v___x_938_, v_type_919_);
v___x_940_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_924_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_Syntax_node5(v___x_924_, v___x_925_, v___x_935_, v_id_918_, v___x_937_, v___x_939_, v___x_941_);
return v___x_942_;
}
case 1:
{
uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_943_ = 0;
v___x_944_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_943_);
lean_dec(v_ref_922_);
v___x_945_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_946_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc_n(v___x_944_, 5);
v___x_947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_944_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_949_ = l_Lean_Syntax_node1(v___x_944_, v___x_948_, v_id_918_);
v___x_950_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_944_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_Syntax_node2(v___x_944_, v___x_948_, v___x_951_, v_type_919_);
v___x_953_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_944_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_Syntax_node4(v___x_944_, v___x_945_, v___x_947_, v___x_949_, v___x_952_, v___x_954_);
return v___x_955_;
}
case 2:
{
uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_956_ = 0;
v___x_957_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_956_);
lean_dec(v_ref_922_);
v___x_958_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_959_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc_n(v___x_957_, 5);
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_957_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_962_ = l_Lean_Syntax_node1(v___x_957_, v___x_961_, v_id_918_);
v___x_963_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_957_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_Syntax_node2(v___x_957_, v___x_961_, v___x_964_, v_type_919_);
v___x_966_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
v___x_967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_957_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_Syntax_node4(v___x_957_, v___x_958_, v___x_960_, v___x_962_, v___x_965_, v___x_967_);
return v___x_968_;
}
default: 
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_969_ = 0;
v___x_970_ = l_Lean_SourceInfo_fromRef(v_ref_922_, v___x_969_);
lean_dec(v_ref_922_);
v___x_971_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_972_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc_n(v___x_970_, 4);
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_975_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_970_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Syntax_node2(v___x_970_, v___x_974_, v_id_918_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_970_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l_Lean_Syntax_node4(v___x_970_, v___x_971_, v___x_973_, v___x_977_, v_type_919_, v___x_979_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* v_x_988_){
_start:
{
lean_object* v_ref_989_; lean_object* v_id_990_; lean_object* v___x_991_; lean_object* v_ref_992_; uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_ref_989_ = lean_ctor_get(v_x_988_, 0);
lean_inc(v_ref_989_);
v_id_990_ = lean_ctor_get(v_x_988_, 1);
lean_inc_n(v_id_990_, 2);
lean_dec_ref(v_x_988_);
v___x_991_ = lean_box(0);
v_ref_992_ = l_Lean_replaceRef(v_ref_989_, v___x_991_);
lean_dec(v_ref_989_);
v___x_993_ = 0;
v___x_994_ = l_Lean_SourceInfo_fromRef(v_ref_992_, v___x_993_);
lean_dec(v_ref_992_);
v___x_995_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__1));
v___x_996_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc_n(v___x_994_, 3);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__2));
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_994_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node5(v___x_994_, v___x_995_, v___x_997_, v_id_990_, v___x_999_, v_id_990_, v___x_1001_);
return v___x_1002_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Binder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
