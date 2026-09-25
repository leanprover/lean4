// Lean compiler output
// Module: Lean.Elab.Arg
// Imports: public import Lean.Elab.Term
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_instInhabitedArg_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedArg_default = (const lean_object*)&l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedArg = (const lean_object*)&l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_instToStringArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instToStringArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_instToStringArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToStringArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instToStringArg = (const lean_object*)&l_Lean_Elab_Term_instToStringArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_instToMessageDataArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instToMessageDataArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_instToMessageDataArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instToMessageDataArg = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg_default = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_instToStringNamedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instToStringNamedArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_instToStringNamedArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToStringNamedArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instToStringNamedArg = (const lean_object*)&l_Lean_Elab_Term_instToStringNamedArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataNamedArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_addNamedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Argument `"};
static const lean_object* l_Lean_Elab_Term_addNamedArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_addNamedArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Term_addNamedArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
static const lean_string_object l_Lean_Elab_Term_addNamedArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` was already set"};
static const lean_object* l_Lean_Elab_Term_addNamedArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_addNamedArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_addNamedArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unexpected '..'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Term_expandArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_expandArgs___closed__0 = (const lean_object*)&l_Lean_Elab_Term_expandArgs___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_expandArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_expandArgs___closed__0_value),((lean_object*)&l_Lean_Elab_Term_expandArgs___closed__0_value)}};
static const lean_object* l_Lean_Elab_Term_expandArgs___closed__1 = (const lean_object*)&l_Lean_Elab_Term_expandArgs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Term_Arg_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_val_8_; lean_object* v___x_9_; 
v_val_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_val_8_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; 
v_val_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_val_10_);
lean_dec_ref_known(v_t_6_, 1);
v___x_11_ = lean_apply_1(v_k_7_, v_val_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Term_Arg_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim___redArg(lean_object* v_t_24_, lean_object* v_stx_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_24_, v_stx_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_stx_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_28_, v_stx_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim___redArg(lean_object* v_t_32_, lean_object* v_expr_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_32_, v_expr_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_expr_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_36_, v_expr_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringArg___lam__0(lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_val_45_; lean_object* v___x_46_; uint8_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_val_45_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v_x_44_, 1);
v___x_46_ = lean_box(0);
v___x_47_ = 0;
v___x_48_ = l_Lean_Syntax_formatStx(v_val_45_, v___x_46_, v___x_47_);
v___x_49_ = l_Std_Format_defWidth;
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Std_Format_pretty(v___x_48_, v___x_49_, v___x_50_, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
v_val_52_ = lean_ctor_get(v_x_44_, 0);
lean_inc_ref(v_val_52_);
lean_dec_ref_known(v_x_44_, 1);
v___x_53_ = lean_expr_dbg_to_string(v_val_52_);
lean_dec_ref(v_val_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataArg___lam__0(lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v_val_57_; lean_object* v___x_58_; 
v_val_57_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_x_56_, 1);
v___x_58_ = l_Lean_MessageData_ofSyntax(v_val_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
v_val_59_ = lean_ctor_get(v_x_56_, 0);
lean_inc_ref(v_val_59_);
lean_dec_ref_known(v_x_56_, 1);
v___x_60_ = l_Lean_MessageData_ofExpr(v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0(lean_object* v_s_73_){
_start:
{
lean_object* v_name_74_; lean_object* v_val_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___y_83_; 
v_name_74_ = lean_ctor_get(v_s_73_, 1);
lean_inc(v_name_74_);
v_val_75_ = lean_ctor_get(v_s_73_, 2);
lean_inc_ref(v_val_75_);
lean_dec_ref(v_s_73_);
v___x_76_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0));
v___x_77_ = 1;
v___x_78_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_74_, v___x_77_);
v___x_79_ = lean_string_append(v___x_76_, v___x_78_);
lean_dec_ref(v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1));
v___x_81_ = lean_string_append(v___x_79_, v___x_80_);
if (lean_obj_tag(v_val_75_) == 0)
{
lean_object* v_val_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_val_87_ = lean_ctor_get(v_val_75_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v_val_75_, 1);
v___x_88_ = lean_box(0);
v___x_89_ = 0;
v___x_90_ = l_Lean_Syntax_formatStx(v_val_87_, v___x_88_, v___x_89_);
v___x_91_ = l_Std_Format_defWidth;
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = l_Std_Format_pretty(v___x_90_, v___x_91_, v___x_92_, v___x_92_);
v___y_83_ = v___x_93_;
goto v___jp_82_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_95_; 
v_val_94_ = lean_ctor_get(v_val_75_, 0);
lean_inc_ref(v_val_94_);
lean_dec_ref_known(v_val_75_, 1);
v___x_95_ = lean_expr_dbg_to_string(v_val_94_);
lean_dec_ref(v_val_94_);
v___y_83_ = v___x_95_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_string_append(v___x_81_, v___y_83_);
lean_dec_ref(v___y_83_);
v___x_85_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2));
v___x_86_ = lean_string_append(v___x_84_, v___x_85_);
return v___x_86_;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0));
v___x_99_ = l_Lean_stringToMessageData(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1));
v___x_101_ = l_Lean_stringToMessageData(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2));
v___x_103_ = l_Lean_stringToMessageData(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0(lean_object* v_s_104_){
_start:
{
lean_object* v_name_105_; lean_object* v_val_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___y_113_; 
v_name_105_ = lean_ctor_get(v_s_104_, 1);
lean_inc(v_name_105_);
v_val_106_ = lean_ctor_get(v_s_104_, 2);
lean_inc_ref(v_val_106_);
lean_dec_ref(v_s_104_);
v___x_107_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0);
v___x_108_ = l_Lean_MessageData_ofName(v_name_105_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1);
v___x_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
if (lean_obj_tag(v_val_106_) == 0)
{
lean_object* v_val_117_; lean_object* v___x_118_; 
v_val_117_ = lean_ctor_get(v_val_106_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v_val_106_, 1);
v___x_118_ = l_Lean_MessageData_ofSyntax(v_val_117_);
v___y_113_ = v___x_118_;
goto v___jp_112_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
v_val_119_ = lean_ctor_get(v_val_106_, 0);
lean_inc_ref(v_val_119_);
lean_dec_ref_known(v_val_106_, 1);
v___x_120_ = l_Lean_MessageData_ofExpr(v_val_119_);
v___y_113_ = v___x_120_;
goto v___jp_112_;
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_111_);
lean_ctor_set(v___x_114_, 1, v___y_113_);
v___x_115_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_toCold_132_; lean_object* v_mctx_133_; lean_object* v_lctx_134_; lean_object* v_options_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_toCold_132_ = lean_ctor_get(v___y_126_, 0);
v_mctx_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_133_);
lean_dec(v___x_131_);
v_lctx_134_ = lean_ctor_get(v___y_124_, 2);
v_options_135_ = lean_ctor_get(v_toCold_132_, 2);
lean_inc_ref(v_options_135_);
lean_inc_ref(v_lctx_134_);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v_env_130_);
lean_ctor_set(v___x_136_, 1, v_mctx_133_);
lean_ctor_set(v___x_136_, 2, v_lctx_134_);
lean_ctor_set(v___x_136_, 3, v_options_135_);
v___x_137_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_msgData_123_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msgData_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 2);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc(v_ref_152_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_ref_152_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(lean_object* v_ref_170_, lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_toCold_177_; lean_object* v_currRecDepth_178_; lean_object* v_ref_179_; uint16_t v_optionFlags_180_; uint8_t v_suppressElabErrors_181_; uint8_t v_isRecordingDeps_182_; lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_toCold_177_ = lean_ctor_get(v___y_174_, 0);
v_currRecDepth_178_ = lean_ctor_get(v___y_174_, 1);
v_ref_179_ = lean_ctor_get(v___y_174_, 2);
v_optionFlags_180_ = lean_ctor_get_uint16(v___y_174_, sizeof(void*)*3);
v_suppressElabErrors_181_ = lean_ctor_get_uint8(v___y_174_, sizeof(void*)*3 + 2);
v_isRecordingDeps_182_ = lean_ctor_get_uint8(v___y_174_, sizeof(void*)*3 + 3);
v_ref_183_ = l_Lean_replaceRef(v_ref_170_, v_ref_179_);
lean_inc(v_currRecDepth_178_);
lean_inc_ref(v_toCold_177_);
v___x_184_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_184_, 0, v_toCold_177_);
lean_ctor_set(v___x_184_, 1, v_currRecDepth_178_);
lean_ctor_set(v___x_184_, 2, v_ref_183_);
lean_ctor_set_uint16(v___x_184_, sizeof(void*)*3, v_optionFlags_180_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 2, v_suppressElabErrors_181_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 3, v_isRecordingDeps_182_);
v___x_185_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_171_, v___y_172_, v___y_173_, v___x_184_, v___y_175_);
lean_dec_ref_known(v___x_184_, 3);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(lean_object* v_ref_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_186_, v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v_ref_186_);
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(lean_object* v_namedArg_194_, lean_object* v_as_195_, size_t v_i_196_, size_t v_stop_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_eq(v_i_196_, v_stop_197_);
if (v___x_198_ == 0)
{
lean_object* v_name_199_; lean_object* v___x_200_; lean_object* v_name_201_; uint8_t v___x_202_; 
v_name_199_ = lean_ctor_get(v_namedArg_194_, 1);
v___x_200_ = lean_array_uget_borrowed(v_as_195_, v_i_196_);
v_name_201_ = lean_ctor_get(v___x_200_, 1);
v___x_202_ = lean_name_eq(v_name_199_, v_name_201_);
if (v___x_202_ == 0)
{
size_t v___x_203_; size_t v___x_204_; 
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_add(v_i_196_, v___x_203_);
v_i_196_ = v___x_204_;
goto _start;
}
else
{
return v___x_202_;
}
}
else
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(lean_object* v_namedArg_207_, lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_stop_210_){
_start:
{
size_t v_i_boxed_211_; size_t v_stop_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_i_boxed_211_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_stop_boxed_212_ = lean_unbox_usize(v_stop_210_);
lean_dec(v_stop_210_);
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_207_, v_as_208_, v_i_boxed_211_, v_stop_boxed_212_);
lean_dec_ref(v_as_208_);
lean_dec_ref(v_namedArg_207_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__0));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__2));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* v_namedArgs_221_, lean_object* v_namedArg_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_array_get_size(v_namedArgs_221_);
v___x_233_ = lean_nat_dec_lt(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
goto v___jp_228_;
}
else
{
if (v___x_233_ == 0)
{
goto v___jp_228_;
}
else
{
size_t v___x_234_; size_t v___x_235_; uint8_t v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_232_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_222_, v_namedArgs_221_, v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
goto v___jp_228_;
}
else
{
lean_object* v_ref_237_; lean_object* v_name_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_namedArgs_221_);
v_ref_237_ = lean_ctor_get(v_namedArg_222_, 0);
lean_inc(v_ref_237_);
v_name_238_ = lean_ctor_get(v_namedArg_222_, 1);
lean_inc(v_name_238_);
lean_dec_ref(v_namedArg_222_);
v___x_239_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__1, &l_Lean_Elab_Term_addNamedArg___closed__1_once, _init_l_Lean_Elab_Term_addNamedArg___closed__1);
v___x_240_ = l_Lean_MessageData_ofName(v_name_238_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__3, &l_Lean_Elab_Term_addNamedArg___closed__3_once, _init_l_Lean_Elab_Term_addNamedArg___closed__3);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_237_, v___x_243_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_ref_237_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
v___jp_228_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_array_push(v_namedArgs_221_, v_namedArg_222_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* v_namedArgs_253_, lean_object* v_namedArg_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_Term_addNamedArg(v_namedArgs_253_, v_namedArg_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_object* v_00_u03b1_261_, lean_object* v_ref_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_262_, v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(lean_object* v_00_u03b1_270_, lean_object* v_ref_271_, lean_object* v_msg_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(v_00_u03b1_270_, v_ref_271_, v_msg_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v_ref_271_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_object* v_00_u03b1_279_, lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(lean_object* v_00_u03b1_287_, lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(v_00_u03b1_287_, v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(lean_object* v_as_313_, size_t v_i_314_, size_t v_stop_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_a_323_; uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_eq(v_i_314_, v_stop_315_);
if (v___x_327_ == 0)
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_369_; 
v_fst_328_ = lean_ctor_get(v_b_316_, 0);
v_snd_329_ = lean_ctor_get(v_b_316_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_b_316_);
if (v_isSharedCheck_369_ == 0)
{
v___x_331_ = v_b_316_;
v_isShared_332_ = v_isSharedCheck_369_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snd_329_);
lean_inc(v_fst_328_);
lean_dec(v_b_316_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_369_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_array_uget_borrowed(v_as_313_, v_i_314_);
lean_inc(v___x_333_);
v___x_334_ = l_Lean_Syntax_getKind(v___x_333_);
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4));
v___x_336_ = lean_name_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
v___x_338_ = lean_name_eq(v___x_334_, v___x_337_);
lean_dec(v___x_334_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
lean_inc(v___x_333_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_333_);
v___x_340_ = lean_array_push(v_snd_329_, v___x_339_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_340_);
v___x_342_ = v___x_331_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_fst_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
v_a_323_ = v___x_342_;
goto v___jp_322_;
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_del_object(v___x_331_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
v___x_344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8);
v___x_345_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v___x_333_, v___x_344_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_a_323_ = v_a_346_;
goto v___jp_322_;
}
else
{
return v___x_345_;
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_name_350_; lean_object* v___x_351_; lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v___x_334_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = l_Lean_Syntax_getArg(v___x_333_, v___x_347_);
v___x_349_ = l_Lean_Syntax_getId(v___x_348_);
lean_dec(v___x_348_);
v_name_350_ = l_Lean_Name_eraseMacroScopes(v___x_349_);
lean_dec(v___x_349_);
v___x_351_ = lean_unsigned_to_nat(3u);
v_val_352_ = l_Lean_Syntax_getArg(v___x_333_, v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_val_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_333_);
v___x_355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_333_);
lean_ctor_set(v___x_355_, 1, v_name_350_);
lean_ctor_set(v___x_355_, 2, v___x_353_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
v___x_356_ = l_Lean_Elab_Term_addNamedArg(v_fst_328_, v___x_355_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v_a_357_);
v___x_359_ = v___x_331_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_357_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_snd_329_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
v_a_323_ = v___x_359_;
goto v___jp_322_;
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_del_object(v___x_331_);
lean_dec(v_snd_329_);
v_a_361_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_356_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_356_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v_b_316_);
return v___x_370_;
}
v___jp_322_:
{
size_t v___x_324_; size_t v___x_325_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_314_, v___x_324_);
v_i_314_ = v___x_325_;
v_b_316_ = v_a_323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_371_, v_i_boxed_380_, v_stop_boxed_381_, v_b_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v_as_371_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs(lean_object* v_args_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v___y_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v_fst_416_; uint8_t v_snd_417_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_array_get_size(v_args_387_);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_nat_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_sub(v___x_430_, v___x_434_);
v___x_436_ = lean_array_get_borrowed(v___x_433_, v_args_387_, v___x_435_);
lean_dec(v___x_435_);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
lean_inc(v___x_436_);
v___x_438_ = l_Lean_Syntax_isOfKind(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
v_fst_416_ = v_args_387_;
v_snd_417_ = v___x_438_;
goto v___jp_415_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_array_pop(v_args_387_);
v_fst_416_ = v___x_439_;
v_snd_417_ = v___x_438_;
goto v___jp_415_;
}
}
else
{
uint8_t v___x_440_; 
v___x_440_ = 0;
v_fst_416_ = v_args_387_;
v_snd_417_ = v___x_440_;
goto v___jp_415_;
}
v___jp_393_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = lean_box(v___y_394_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_snd_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_fst_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
v___jp_401_:
{
if (lean_obj_tag(v___y_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_fst_405_; lean_object* v_snd_406_; 
v_a_404_ = lean_ctor_get(v___y_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___y_403_, 1);
v_fst_405_ = lean_ctor_get(v_a_404_, 0);
lean_inc(v_fst_405_);
v_snd_406_ = lean_ctor_get(v_a_404_, 1);
lean_inc(v_snd_406_);
lean_dec(v_a_404_);
v___y_394_ = v___y_402_;
v_fst_395_ = v_fst_405_;
v_snd_396_ = v_snd_406_;
goto v___jp_393_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___y_403_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___y_403_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___y_403_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___y_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
v___jp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__0));
v___x_420_ = lean_array_get_size(v_fst_416_);
v___x_421_ = lean_nat_dec_lt(v___x_418_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec_ref(v_fst_416_);
v___y_394_ = v_snd_417_;
v_fst_395_ = v___x_419_;
v_snd_396_ = v___x_419_;
goto v___jp_393_;
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__1));
v___x_423_ = lean_nat_dec_le(v___x_420_, v___x_420_);
if (v___x_423_ == 0)
{
if (v___x_421_ == 0)
{
lean_dec_ref(v_fst_416_);
v___y_394_ = v_snd_417_;
v_fst_395_ = v___x_419_;
v_snd_396_ = v___x_419_;
goto v___jp_393_;
}
else
{
size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v___x_424_ = ((size_t)0ULL);
v___x_425_ = lean_usize_of_nat(v___x_420_);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_416_, v___x_424_, v___x_425_, v___x_422_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec_ref(v_fst_416_);
v___y_402_ = v_snd_417_;
v___y_403_ = v___x_426_;
goto v___jp_401_;
}
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_420_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_416_, v___x_427_, v___x_428_, v___x_422_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec_ref(v_fst_416_);
v___y_402_ = v_snd_417_;
v___y_403_ = v___x_429_;
goto v___jp_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object* v_args_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_Term_expandArgs(v_args_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp(lean_object* v_stx_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_stx_448_, v___x_454_);
v___x_456_ = l_Lean_Syntax_getArgs(v___x_455_);
lean_dec(v___x_455_);
v___x_457_ = l_Lean_Elab_Term_expandArgs(v___x_456_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_468_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_468_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = l_Lean_Syntax_getArg(v_stx_448_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_464_);
v___x_466_ = v___x_460_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_457_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_457_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* v_stx_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Elab_Term_expandApp(v_stx_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_stx_477_);
return v_res_483_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Arg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Arg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Arg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Arg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Arg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Arg(builtin);
}
#ifdef __cplusplus
}
#endif
