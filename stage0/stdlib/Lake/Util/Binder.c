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
lean_dec_ref(v_a_302_);
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
lean_inc(v_quotContext_307_);
v_currMacroScope_308_ = lean_ctor_get(v_a_302_, 2);
lean_inc(v_currMacroScope_308_);
v_ref_309_ = lean_ctor_get(v_a_302_, 5);
lean_inc(v_ref_309_);
lean_dec_ref(v_a_302_);
v___x_310_ = 0;
v___x_311_ = l_Lean_SourceInfo_fromRef(v_ref_309_, v___x_310_);
lean_dec(v_ref_309_);
v___x_312_ = lean_obj_once(&l_Lake_expandBinderIdent___closed__1, &l_Lake_expandBinderIdent___closed__1_once, _init_l_Lake_expandBinderIdent___closed__1);
v___x_313_ = ((lean_object*)(l_Lake_expandBinderIdent___closed__2));
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
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* v_stx_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Lean_Syntax_isNone(v_stx_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l_Lean_Syntax_getArg(v_stx_318_, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = l_Lake_mkHoleFrom(v_stx_318_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* v_stx_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lake_expandOptIdent(v_stx_323_);
lean_dec(v_stx_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* v_ref_325_, lean_object* v_stx_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = l_Lean_Syntax_getNumArgs(v_stx_326_);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_nat_dec_eq(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = l_Lean_Syntax_getArg(v_stx_326_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = l_Lake_mkHoleFrom(v_ref_325_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* v_ref_333_, lean_object* v_stx_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_expandBinderType(v_ref_333_, v_stx_334_);
lean_dec(v_stx_334_);
lean_dec(v_ref_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* v_optBinderModifier_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Syntax_getOptional_x3f(v_optBinderModifier_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_val_339_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_val_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* v_optBinderModifier_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lake_expandBinderModifier(v_optBinderModifier_347_);
lean_dec(v_optBinderModifier_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(lean_object* v___x_349_, lean_object* v_stx_350_, lean_object* v_as_351_, size_t v_i_352_, size_t v_stop_353_, lean_object* v_b_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_352_, v_stop_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_array_uget_borrowed(v_as_351_, v_i_352_);
lean_inc_ref(v___y_355_);
lean_inc(v___x_358_);
v___x_359_ = l_Lake_expandBinderIdent(v___x_358_, v___y_355_, v___y_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v_a_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; size_t v___x_367_; size_t v___x_368_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
v_a_361_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_a_361_);
lean_dec_ref(v___x_359_);
v___x_362_ = l_Lake_expandBinderType(v___x_358_, v___x_349_);
v___x_363_ = 1;
v___x_364_ = lean_box(0);
lean_inc(v_stx_350_);
v___x_365_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_365_, 0, v_stx_350_);
lean_ctor_set(v___x_365_, 1, v_a_360_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*4, v___x_363_);
v___x_366_ = lean_array_push(v_b_354_, v___x_365_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_352_, v___x_367_);
v_i_352_ = v___x_368_;
v_b_354_ = v___x_366_;
v___y_356_ = v_a_361_;
goto _start;
}
else
{
lean_object* v_a_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_b_354_);
lean_dec(v_stx_350_);
v_a_370_ = lean_ctor_get(v___x_359_, 0);
v_a_371_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_359_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_inc(v_a_370_);
lean_dec(v___x_359_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v_stx_350_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_b_354_);
lean_ctor_set(v___x_379_, 1, v___y_356_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1___boxed(lean_object* v___x_380_, lean_object* v_stx_381_, lean_object* v_as_382_, lean_object* v_i_383_, lean_object* v_stop_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
size_t v_i_boxed_388_; size_t v_stop_boxed_389_; lean_object* v_res_390_; 
v_i_boxed_388_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_stop_boxed_389_ = lean_unbox_usize(v_stop_384_);
lean_dec(v_stop_384_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_380_, v_stx_381_, v_as_382_, v_i_boxed_388_, v_stop_boxed_389_, v_b_385_, v___y_386_, v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_as_382_);
lean_dec(v___x_380_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(lean_object* v___x_391_, lean_object* v_stx_392_, lean_object* v___x_393_, lean_object* v_as_394_, size_t v_i_395_, size_t v_stop_396_, lean_object* v_b_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_395_, v_stop_396_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_array_uget_borrowed(v_as_394_, v_i_395_);
lean_inc_ref(v___y_398_);
lean_inc(v___x_401_);
v___x_402_ = l_Lake_expandBinderIdent(v___x_401_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; size_t v___x_409_; size_t v___x_410_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
v_a_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_a_404_);
lean_dec_ref(v___x_402_);
v___x_405_ = l_Lake_expandBinderType(v___x_401_, v___x_391_);
v___x_406_ = 0;
lean_inc(v___x_393_);
lean_inc(v_stx_392_);
v___x_407_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_407_, 0, v_stx_392_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
lean_ctor_set(v___x_407_, 3, v___x_393_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*4, v___x_406_);
v___x_408_ = lean_array_push(v_b_397_, v___x_407_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_add(v_i_395_, v___x_409_);
v_i_395_ = v___x_410_;
v_b_397_ = v___x_408_;
v___y_399_ = v_a_404_;
goto _start;
}
else
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v_b_397_);
lean_dec(v___x_393_);
lean_dec(v_stx_392_);
v_a_412_ = lean_ctor_get(v___x_402_, 0);
v_a_413_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_402_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_inc(v_a_412_);
lean_dec(v___x_402_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_412_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v___x_393_);
lean_dec(v_stx_392_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_b_397_);
lean_ctor_set(v___x_421_, 1, v___y_399_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2___boxed(lean_object* v___x_422_, lean_object* v_stx_423_, lean_object* v___x_424_, lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_stop_427_, lean_object* v_b_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
size_t v_i_boxed_431_; size_t v_stop_boxed_432_; lean_object* v_res_433_; 
v_i_boxed_431_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_stop_boxed_432_ = lean_unbox_usize(v_stop_427_);
lean_dec(v_stop_427_);
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_422_, v_stx_423_, v___x_424_, v_as_425_, v_i_boxed_431_, v_stop_boxed_432_, v_b_428_, v___y_429_, v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_as_425_);
lean_dec(v___x_422_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(lean_object* v___x_434_, lean_object* v_stx_435_, lean_object* v_as_436_, size_t v_i_437_, size_t v_stop_438_, lean_object* v_b_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_eq(v_i_437_, v_stop_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_array_uget_borrowed(v_as_436_, v_i_437_);
lean_inc_ref(v___y_440_);
lean_inc(v___x_443_);
v___x_444_ = l_Lake_expandBinderIdent(v___x_443_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_a_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; size_t v___x_452_; size_t v___x_453_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
v_a_446_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_a_446_);
lean_dec_ref(v___x_444_);
v___x_447_ = l_Lake_expandBinderType(v___x_443_, v___x_434_);
v___x_448_ = 2;
v___x_449_ = lean_box(0);
lean_inc(v_stx_435_);
v___x_450_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_450_, 0, v_stx_435_);
lean_ctor_set(v___x_450_, 1, v_a_445_);
lean_ctor_set(v___x_450_, 2, v___x_447_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*4, v___x_448_);
v___x_451_ = lean_array_push(v_b_439_, v___x_450_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_437_, v___x_452_);
v_i_437_ = v___x_453_;
v_b_439_ = v___x_451_;
v___y_441_ = v_a_446_;
goto _start;
}
else
{
lean_object* v_a_455_; lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_b_439_);
lean_dec(v_stx_435_);
v_a_455_ = lean_ctor_get(v___x_444_, 0);
v_a_456_ = lean_ctor_get(v___x_444_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_444_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_inc(v_a_455_);
lean_dec(v___x_444_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_455_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_stx_435_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_b_439_);
lean_ctor_set(v___x_464_, 1, v___y_441_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0___boxed(lean_object* v___x_465_, lean_object* v_stx_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_stop_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
size_t v_i_boxed_473_; size_t v_stop_boxed_474_; lean_object* v_res_475_; 
v_i_boxed_473_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_stop_boxed_474_ = lean_unbox_usize(v_stop_469_);
lean_dec(v_stop_469_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_465_, v_stx_466_, v_as_467_, v_i_boxed_473_, v_stop_boxed_474_, v_b_470_, v___y_471_, v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec_ref(v_as_467_);
lean_dec(v___x_465_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore(lean_object* v_binders_500_, lean_object* v_stx_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_k_504_; uint8_t v___y_506_; uint8_t v___x_661_; 
lean_inc(v_stx_501_);
v_k_504_ = l_Lean_Syntax_getKind(v_stx_501_);
v___x_661_ = l_Lean_Syntax_isIdent(v_stx_501_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lake_mkHoleFrom___closed__4));
v___x_663_ = lean_name_eq(v_k_504_, v___x_662_);
v___y_506_ = v___x_663_;
goto v___jp_505_;
}
else
{
v___y_506_ = v___x_661_;
goto v___jp_505_;
}
v___jp_505_:
{
if (v___y_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_508_ = lean_name_eq(v_k_504_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_510_ = lean_name_eq(v_k_504_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_512_ = lean_name_eq(v_k_504_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_514_ = lean_name_eq(v_k_504_, v___x_513_);
lean_dec(v_k_504_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec(v_stx_501_);
lean_dec_ref(v_binders_500_);
v___x_515_ = l_Lean_Macro_throwUnsupported___redArg(v_a_503_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_id_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_534_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_516_);
v_id_518_ = l_Lake_expandOptIdent(v___x_517_);
lean_dec(v___x_517_);
lean_inc_ref(v_a_502_);
v___x_519_ = l_Lake_expandBinderIdent(v_id_518_, v_a_502_, v_a_503_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_a_521_ = lean_ctor_get(v___x_519_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_534_ == 0)
{
v___x_523_ = v___x_519_;
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_534_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_type_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v_type_526_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_525_);
v___x_527_ = 3;
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_529_, 0, v_stx_501_);
lean_ctor_set(v___x_529_, 1, v_a_520_);
lean_ctor_set(v___x_529_, 2, v_type_526_);
lean_ctor_set(v___x_529_, 3, v___x_528_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*4, v___x_527_);
v___x_530_ = lean_array_push(v_binders_500_, v___x_529_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_530_);
v___x_532_ = v___x_523_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_a_521_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_k_504_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_535_);
v___x_537_ = l_Lake_getBinderIds(v___x_536_, v_a_502_, v_a_503_);
lean_dec(v___x_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_561_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_a_539_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_561_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_561_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_561_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_a_538_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v_a_538_);
lean_dec(v_stx_501_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_binders_500_);
v___x_547_ = v___x_541_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_a_539_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(2u);
v___x_550_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_549_);
v___x_551_ = lean_nat_dec_le(v___x_544_, v___x_544_);
if (v___x_551_ == 0)
{
if (v___x_545_ == 0)
{
lean_object* v___x_553_; 
lean_dec(v___x_550_);
lean_dec(v_a_538_);
lean_dec(v_stx_501_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_binders_500_);
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_a_539_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
lean_del_object(v___x_541_);
v___x_555_ = ((size_t)0ULL);
v___x_556_ = lean_usize_of_nat(v___x_544_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_550_, v_stx_501_, v_a_538_, v___x_555_, v___x_556_, v_binders_500_, v_a_502_, v_a_539_);
lean_dec(v_a_538_);
lean_dec(v___x_550_);
return v___x_557_;
}
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_541_);
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_544_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__0(v___x_550_, v_stx_501_, v_a_538_, v___x_558_, v___x_559_, v_binders_500_, v_a_502_, v_a_539_);
lean_dec(v_a_538_);
lean_dec(v___x_550_);
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_stx_501_);
lean_dec_ref(v_binders_500_);
v_a_562_ = lean_ctor_get(v___x_537_, 0);
v_a_563_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_537_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_inc(v_a_562_);
lean_dec(v___x_537_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_k_504_);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_571_);
v___x_573_ = l_Lake_getBinderIds(v___x_572_, v_a_502_, v_a_503_);
lean_dec(v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_597_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_a_575_ = lean_ctor_get(v___x_573_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_597_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_597_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_597_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_array_get_size(v_a_574_);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_583_; 
lean_dec(v_a_574_);
lean_dec(v_stx_501_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_binders_500_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_a_575_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_unsigned_to_nat(2u);
v___x_586_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_585_);
v___x_587_ = lean_nat_dec_le(v___x_580_, v___x_580_);
if (v___x_587_ == 0)
{
if (v___x_581_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v___x_586_);
lean_dec(v_a_574_);
lean_dec(v_stx_501_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_binders_500_);
v___x_589_ = v___x_577_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_575_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
lean_del_object(v___x_577_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = lean_usize_of_nat(v___x_580_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_586_, v_stx_501_, v_a_574_, v___x_591_, v___x_592_, v_binders_500_, v_a_502_, v_a_575_);
lean_dec(v_a_574_);
lean_dec(v___x_586_);
return v___x_593_;
}
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_577_);
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_580_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__1(v___x_586_, v_stx_501_, v_a_574_, v___x_594_, v___x_595_, v_binders_500_, v_a_502_, v_a_575_);
lean_dec(v_a_574_);
lean_dec(v___x_586_);
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_stx_501_);
lean_dec_ref(v_binders_500_);
v_a_598_ = lean_ctor_get(v___x_573_, 0);
v_a_599_ = lean_ctor_get(v___x_573_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_573_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_573_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_k_504_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_607_);
v___x_609_ = l_Lake_getBinderIds(v___x_608_, v_a_502_, v_a_503_);
lean_dec(v___x_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_636_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_a_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_636_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_636_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_636_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_a_610_);
v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_619_; 
lean_dec(v_a_610_);
lean_dec(v_stx_501_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_binders_500_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_a_611_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_621_ = lean_unsigned_to_nat(2u);
v___x_622_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_621_);
v___x_623_ = lean_unsigned_to_nat(3u);
v___x_624_ = l_Lean_Syntax_getArg(v_stx_501_, v___x_623_);
v___x_625_ = l_Lake_expandBinderModifier(v___x_624_);
lean_dec(v___x_624_);
v___x_626_ = lean_nat_dec_le(v___x_616_, v___x_616_);
if (v___x_626_ == 0)
{
if (v___x_617_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v___x_625_);
lean_dec(v___x_622_);
lean_dec(v_a_610_);
lean_dec(v_stx_501_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_binders_500_);
v___x_628_ = v___x_613_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_binders_500_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_611_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
lean_del_object(v___x_613_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = lean_usize_of_nat(v___x_616_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_622_, v_stx_501_, v___x_625_, v_a_610_, v___x_630_, v___x_631_, v_binders_500_, v_a_502_, v_a_611_);
lean_dec(v_a_610_);
lean_dec(v___x_622_);
return v___x_632_;
}
}
else
{
size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; 
lean_del_object(v___x_613_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = lean_usize_of_nat(v___x_616_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinderCore_spec__2(v___x_622_, v_stx_501_, v___x_625_, v_a_610_, v___x_633_, v___x_634_, v_binders_500_, v_a_502_, v_a_611_);
lean_dec(v_a_610_);
lean_dec(v___x_622_);
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_stx_501_);
lean_dec_ref(v_binders_500_);
v_a_637_ = lean_ctor_get(v___x_609_, 0);
v_a_638_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_609_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_inc(v_a_637_);
lean_dec(v___x_609_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v_a_647_; lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_k_504_);
lean_inc_ref(v_a_502_);
lean_inc(v_stx_501_);
v___x_646_ = l_Lake_expandBinderIdent(v_stx_501_, v_a_502_, v_a_503_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_a_648_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_660_ == 0)
{
v___x_650_ = v___x_646_;
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_652_ = l_Lake_mkHoleFrom(v_stx_501_);
v___x_653_ = 0;
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_655_, 0, v_stx_501_);
lean_ctor_set(v___x_655_, 1, v_a_647_);
lean_ctor_set(v___x_655_, 2, v___x_652_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*4, v___x_653_);
v___x_656_ = lean_array_push(v_binders_500_, v___x_655_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_656_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_648_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderCore___boxed(lean_object* v_binders_664_, lean_object* v_stx_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lake_expandBinderCore(v_binders_664_, v_stx_665_, v_a_666_, v_a_667_);
lean_dec_ref(v_a_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder(lean_object* v_stx_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_675_ = l_Lake_expandBinderCore(v___x_674_, v_stx_671_, v_a_672_, v_a_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinder___boxed(lean_object* v_stx_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lake_expandBinder(v_stx_676_, v_a_677_, v_a_678_);
lean_dec_ref(v_a_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
lean_inc(v___x_687_);
v___x_688_ = l_Lake_expandBinderCore(v_b_683_, v___x_687_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v_a_690_; size_t v___x_691_; size_t v___x_692_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
v_a_690_ = lean_ctor_get(v___x_688_, 1);
lean_inc(v_a_690_);
lean_dec_ref(v___x_688_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_681_, v___x_691_);
v_i_681_ = v___x_692_;
v_b_683_ = v_a_689_;
v___y_685_ = v_a_690_;
goto _start;
}
else
{
return v___x_688_;
}
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_b_683_);
lean_ctor_set(v___x_694_, 1, v___y_685_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0___boxed(lean_object* v_as_695_, lean_object* v_i_696_, lean_object* v_stop_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_i_boxed_701_; size_t v_stop_boxed_702_; lean_object* v_res_703_; 
v_i_boxed_701_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_stop_boxed_702_ = lean_unbox_usize(v_stop_697_);
lean_dec(v_stop_697_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_as_695_, v_i_boxed_701_, v_stop_boxed_702_, v_b_698_, v___y_699_, v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_as_695_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* v_stxs_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = ((lean_object*)(l_Lake_expandBinder___closed__0));
v___x_709_ = lean_array_get_size(v_stxs_704_);
v___x_710_ = lean_nat_dec_lt(v___x_707_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v_a_706_);
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = lean_nat_dec_le(v___x_709_, v___x_709_);
if (v___x_712_ == 0)
{
if (v___x_710_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_708_);
lean_ctor_set(v___x_713_, 1, v_a_706_);
return v___x_713_;
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_709_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_704_, v___x_714_, v___x_715_, v___x_708_, v_a_705_, v_a_706_);
return v___x_716_;
}
}
else
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_709_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_expandBinders_spec__0(v_stxs_704_, v___x_717_, v___x_718_, v___x_708_, v_a_705_, v_a_706_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* v_stxs_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lake_expandBinders(v_stxs_720_, v_a_721_, v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec_ref(v_stxs_720_);
return v_res_723_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__4(void){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Array_mkArray0(lean_box(0));
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* v_x_739_){
_start:
{
uint8_t v_info_740_; 
v_info_740_ = lean_ctor_get_uint8(v_x_739_, sizeof(void*)*4);
switch(v_info_740_)
{
case 0:
{
lean_object* v_ref_741_; lean_object* v_id_742_; lean_object* v_type_743_; lean_object* v_modifier_x3f_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___y_757_; 
v_ref_741_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_ref_741_);
v_id_742_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_id_742_);
v_type_743_ = lean_ctor_get(v_x_739_, 2);
lean_inc(v_type_743_);
v_modifier_x3f_744_ = lean_ctor_get(v_x_739_, 3);
lean_inc(v_modifier_x3f_744_);
lean_dec_ref(v_x_739_);
v___x_745_ = 0;
v___x_746_ = l_Lean_SourceInfo_fromRef(v_ref_741_, v___x_745_);
lean_dec(v_ref_741_);
v___x_747_ = ((lean_object*)(l_Lake_expandBinderCore___closed__1));
v___x_748_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc(v___x_746_);
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_746_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_746_);
v___x_751_ = l_Lean_Syntax_node1(v___x_746_, v___x_750_, v_id_742_);
v___x_752_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_746_);
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_746_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_inc(v___x_746_);
v___x_754_ = l_Lean_Syntax_node2(v___x_746_, v___x_750_, v___x_753_, v_type_743_);
v___x_755_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkBinder___closed__4, &l_Lake_BinderSyntaxView_mkBinder___closed__4_once, _init_l_Lake_BinderSyntaxView_mkBinder___closed__4);
if (lean_obj_tag(v_modifier_x3f_744_) == 1)
{
lean_object* v_val_763_; lean_object* v___x_764_; 
v_val_763_ = lean_ctor_get(v_modifier_x3f_744_, 0);
lean_inc(v_val_763_);
lean_dec_ref(v_modifier_x3f_744_);
v___x_764_ = l_Array_mkArray1___redArg(v_val_763_);
v___y_757_ = v___x_764_;
goto v___jp_756_;
}
else
{
lean_object* v___x_765_; 
lean_dec(v_modifier_x3f_744_);
v___x_765_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__6));
v___y_757_ = v___x_765_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = l_Array_append___redArg(v___x_755_, v___y_757_);
lean_dec_ref(v___y_757_);
lean_inc(v___x_746_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_746_);
lean_ctor_set(v___x_759_, 1, v___x_750_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
lean_inc(v___x_746_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_746_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_Syntax_node5(v___x_746_, v___x_747_, v___x_749_, v___x_751_, v___x_754_, v___x_759_, v___x_761_);
return v___x_762_;
}
}
case 1:
{
lean_object* v_ref_766_; lean_object* v_id_767_; lean_object* v_type_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_ref_766_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_ref_766_);
v_id_767_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_id_767_);
v_type_768_ = lean_ctor_get(v_x_739_, 2);
lean_inc(v_type_768_);
lean_dec_ref(v_x_739_);
v___x_769_ = 0;
v___x_770_ = l_Lean_SourceInfo_fromRef(v_ref_766_, v___x_769_);
lean_dec(v_ref_766_);
v___x_771_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_772_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc(v___x_770_);
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_770_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_770_);
v___x_775_ = l_Lean_Syntax_node1(v___x_770_, v___x_774_, v_id_767_);
v___x_776_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_770_);
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_770_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
lean_inc(v___x_770_);
v___x_778_ = l_Lean_Syntax_node2(v___x_770_, v___x_774_, v___x_777_, v_type_768_);
v___x_779_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
lean_inc(v___x_770_);
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_770_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Syntax_node4(v___x_770_, v___x_771_, v___x_773_, v___x_775_, v___x_778_, v___x_780_);
return v___x_781_;
}
case 2:
{
lean_object* v_ref_782_; lean_object* v_id_783_; lean_object* v_type_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_ref_782_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_ref_782_);
v_id_783_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_id_783_);
v_type_784_ = lean_ctor_get(v_x_739_, 2);
lean_inc(v_type_784_);
lean_dec_ref(v_x_739_);
v___x_785_ = 0;
v___x_786_ = l_Lean_SourceInfo_fromRef(v_ref_782_, v___x_785_);
lean_dec(v_ref_782_);
v___x_787_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_788_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc(v___x_786_);
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_786_);
v___x_791_ = l_Lean_Syntax_node1(v___x_786_, v___x_790_, v_id_783_);
v___x_792_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_786_);
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_786_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
lean_inc(v___x_786_);
v___x_794_ = l_Lean_Syntax_node2(v___x_786_, v___x_790_, v___x_793_, v_type_784_);
v___x_795_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
lean_inc(v___x_786_);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_786_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_Syntax_node4(v___x_786_, v___x_787_, v___x_789_, v___x_791_, v___x_794_, v___x_796_);
return v___x_797_;
}
default: 
{
lean_object* v_ref_798_; lean_object* v_id_799_; lean_object* v_type_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_ref_798_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_ref_798_);
v_id_799_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_id_799_);
v_type_800_ = lean_ctor_get(v_x_739_, 2);
lean_inc(v_type_800_);
lean_dec_ref(v_x_739_);
v___x_801_ = 0;
v___x_802_ = l_Lean_SourceInfo_fromRef(v_ref_798_, v___x_801_);
lean_dec(v_ref_798_);
v___x_803_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_804_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc(v___x_802_);
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_807_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_802_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
lean_inc(v___x_802_);
v___x_809_ = l_Lean_Syntax_node2(v___x_802_, v___x_806_, v_id_799_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
lean_inc(v___x_802_);
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_802_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_Syntax_node4(v___x_802_, v___x_803_, v___x_805_, v___x_809_, v_type_800_, v___x_811_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkDepArrow(lean_object* v_res_820_, lean_object* v_self_821_){
_start:
{
lean_object* v_ref_822_; uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_ref_822_ = lean_ctor_get(v_self_821_, 0);
v___x_823_ = 0;
v___x_824_ = l_Lean_SourceInfo_fromRef(v_ref_822_, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__1));
v___x_826_ = l_Lake_BinderSyntaxView_mkBinder(v_self_821_);
v___x_827_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkDepArrow___closed__2));
lean_inc(v___x_824_);
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_824_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_Syntax_node3(v___x_824_, v___x_825_, v___x_826_, v___x_828_, v_res_820_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_, lean_object* v_b_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
v___x_835_ = lean_array_uget_borrowed(v_as_830_, v_i_831_);
lean_inc(v___x_835_);
v___x_836_ = l_Lake_BinderSyntaxView_mkDepArrow(v_b_833_, v___x_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_831_, v___x_837_);
v_i_831_ = v___x_838_;
v_b_833_ = v___x_836_;
goto _start;
}
else
{
return v_b_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0___boxed(lean_object* v_as_840_, lean_object* v_i_841_, lean_object* v_stop_842_, lean_object* v_b_843_){
_start:
{
size_t v_i_boxed_844_; size_t v_stop_boxed_845_; lean_object* v_res_846_; 
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_stop_boxed_845_ = lean_unbox_usize(v_stop_842_);
lean_dec(v_stop_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_as_840_, v_i_boxed_844_, v_stop_boxed_845_, v_b_843_);
lean_dec_ref(v_as_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow(lean_object* v_binders_847_, lean_object* v_res_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_array_get_size(v_binders_847_);
v___x_851_ = lean_nat_dec_lt(v___x_849_, v___x_850_);
if (v___x_851_ == 0)
{
return v_res_848_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = lean_nat_dec_le(v___x_850_, v___x_850_);
if (v___x_852_ == 0)
{
if (v___x_851_ == 0)
{
return v_res_848_;
}
else
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((size_t)0ULL);
v___x_854_ = lean_usize_of_nat(v___x_850_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_847_, v___x_853_, v___x_854_, v_res_848_);
return v___x_855_;
}
}
else
{
size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_856_ = ((size_t)0ULL);
v___x_857_ = lean_usize_of_nat(v___x_850_);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkDepArrow_spec__0(v_binders_847_, v___x_856_, v___x_857_, v_res_848_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkDepArrow___boxed(lean_object* v_binders_859_, lean_object* v_res_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_mkDepArrow(v_binders_859_, v_res_860_);
lean_dec_ref(v_binders_859_);
return v_res_861_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__8));
v___x_882_ = l_String_toRawSubstring_x27(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_883_ = l_Lean_firstFrontendMacroScope;
v___x_884_ = lean_box(0);
v___x_885_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__1));
v___x_886_ = l_Lean_addMacroScope(v___x_885_, v___x_884_, v___x_883_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkFunBinder(lean_object* v_x_912_){
_start:
{
lean_object* v_ref_913_; lean_object* v_id_914_; lean_object* v_type_915_; uint8_t v_info_916_; lean_object* v___x_917_; lean_object* v_ref_918_; 
v_ref_913_ = lean_ctor_get(v_x_912_, 0);
lean_inc(v_ref_913_);
v_id_914_ = lean_ctor_get(v_x_912_, 1);
lean_inc(v_id_914_);
v_type_915_ = lean_ctor_get(v_x_912_, 2);
lean_inc(v_type_915_);
v_info_916_ = lean_ctor_get_uint8(v_x_912_, sizeof(void*)*4);
lean_dec_ref(v_x_912_);
v___x_917_ = lean_box(0);
v_ref_918_ = l_Lean_replaceRef(v_ref_913_, v___x_917_);
lean_dec(v_ref_913_);
switch(v_info_916_)
{
case 0:
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_919_ = 0;
v___x_920_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_919_);
lean_dec(v_ref_918_);
v___x_921_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__3));
v___x_922_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__5));
v___x_923_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc(v___x_920_);
v___x_924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__7));
v___x_926_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__9, &l_Lake_BinderSyntaxView_mkFunBinder___closed__9_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__9);
v___x_927_ = lean_obj_once(&l_Lake_BinderSyntaxView_mkFunBinder___closed__10, &l_Lake_BinderSyntaxView_mkFunBinder___closed__10_once, _init_l_Lake_BinderSyntaxView_mkFunBinder___closed__10);
v___x_928_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkFunBinder___closed__21));
lean_inc(v___x_920_);
v___x_929_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_929_, 0, v___x_920_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
lean_ctor_set(v___x_929_, 2, v___x_927_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
lean_inc(v___x_920_);
v___x_930_ = l_Lean_Syntax_node1(v___x_920_, v___x_925_, v___x_929_);
lean_inc(v___x_920_);
v___x_931_ = l_Lean_Syntax_node2(v___x_920_, v___x_922_, v___x_924_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_920_);
v___x_933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_920_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_920_);
v___x_935_ = l_Lean_Syntax_node1(v___x_920_, v___x_934_, v_type_915_);
v___x_936_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
lean_inc(v___x_920_);
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_920_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_Syntax_node5(v___x_920_, v___x_921_, v___x_931_, v_id_914_, v___x_933_, v___x_935_, v___x_937_);
return v___x_938_;
}
case 1:
{
uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_939_ = 0;
v___x_940_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_939_);
lean_dec(v_ref_918_);
v___x_941_ = ((lean_object*)(l_Lake_expandBinderCore___closed__3));
v___x_942_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__7));
lean_inc(v___x_940_);
v___x_943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_940_);
v___x_945_ = l_Lean_Syntax_node1(v___x_940_, v___x_944_, v_id_914_);
v___x_946_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_940_);
v___x_947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_940_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_inc(v___x_940_);
v___x_948_ = l_Lean_Syntax_node2(v___x_940_, v___x_944_, v___x_947_, v_type_915_);
v___x_949_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__8));
lean_inc(v___x_940_);
v___x_950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_940_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_Syntax_node4(v___x_940_, v___x_941_, v___x_943_, v___x_945_, v___x_948_, v___x_950_);
return v___x_951_;
}
case 2:
{
uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_952_ = 0;
v___x_953_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_952_);
lean_dec(v_ref_918_);
v___x_954_ = ((lean_object*)(l_Lake_expandBinderCore___closed__5));
v___x_955_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__9));
lean_inc(v___x_953_);
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_953_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
lean_inc(v___x_953_);
v___x_958_ = l_Lean_Syntax_node1(v___x_953_, v___x_957_, v_id_914_);
v___x_959_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_953_);
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_953_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
lean_inc(v___x_953_);
v___x_961_ = l_Lean_Syntax_node2(v___x_953_, v___x_957_, v___x_960_, v_type_915_);
v___x_962_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__10));
lean_inc(v___x_953_);
v___x_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_953_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_Syntax_node4(v___x_953_, v___x_954_, v___x_956_, v___x_958_, v___x_961_, v___x_963_);
return v___x_964_;
}
default: 
{
uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_965_ = 0;
v___x_966_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_965_);
lean_dec(v_ref_918_);
v___x_967_ = ((lean_object*)(l_Lake_expandBinderCore___closed__7));
v___x_968_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__11));
lean_inc(v___x_966_);
v___x_969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__2));
v___x_971_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__3));
lean_inc(v___x_966_);
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_966_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_inc(v___x_966_);
v___x_973_ = l_Lean_Syntax_node2(v___x_966_, v___x_970_, v_id_914_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__12));
lean_inc(v___x_966_);
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_966_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_Syntax_node4(v___x_966_, v___x_967_, v___x_969_, v___x_973_, v_type_915_, v___x_975_);
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* v_x_984_){
_start:
{
lean_object* v_ref_985_; lean_object* v_id_986_; lean_object* v___x_987_; lean_object* v_ref_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_ref_985_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_ref_985_);
v_id_986_ = lean_ctor_get(v_x_984_, 1);
lean_inc(v_id_986_);
lean_dec_ref(v_x_984_);
v___x_987_ = lean_box(0);
v_ref_988_ = l_Lean_replaceRef(v_ref_985_, v___x_987_);
lean_dec(v_ref_985_);
v___x_989_ = 0;
v___x_990_ = l_Lean_SourceInfo_fromRef(v_ref_988_, v___x_989_);
lean_dec(v_ref_988_);
v___x_991_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__1));
v___x_992_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__0));
lean_inc(v___x_990_);
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_990_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkArgument___closed__2));
lean_inc(v___x_990_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_990_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lake_BinderSyntaxView_mkBinder___closed__5));
lean_inc(v___x_990_);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_990_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_inc(v_id_986_);
v___x_998_ = l_Lean_Syntax_node5(v___x_990_, v___x_991_, v___x_993_, v_id_986_, v___x_995_, v_id_986_, v___x_997_);
return v___x_998_;
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
