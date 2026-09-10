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
lean_object* v_toCold_177_; lean_object* v_currRecDepth_178_; lean_object* v_ref_179_; uint8_t v_diag_180_; uint8_t v_suppressElabErrors_181_; lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toCold_177_ = lean_ctor_get(v___y_174_, 0);
v_currRecDepth_178_ = lean_ctor_get(v___y_174_, 1);
v_ref_179_ = lean_ctor_get(v___y_174_, 2);
v_diag_180_ = lean_ctor_get_uint8(v___y_174_, sizeof(void*)*3);
v_suppressElabErrors_181_ = lean_ctor_get_uint8(v___y_174_, sizeof(void*)*3 + 1);
v_ref_182_ = l_Lean_replaceRef(v_ref_170_, v_ref_179_);
lean_inc(v_currRecDepth_178_);
lean_inc_ref(v_toCold_177_);
v___x_183_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_183_, 0, v_toCold_177_);
lean_ctor_set(v___x_183_, 1, v_currRecDepth_178_);
lean_ctor_set(v___x_183_, 2, v_ref_182_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3, v_diag_180_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*3 + 1, v_suppressElabErrors_181_);
v___x_184_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_171_, v___y_172_, v___y_173_, v___x_183_, v___y_175_);
lean_dec_ref_known(v___x_183_, 3);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(lean_object* v_ref_185_, lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_185_, v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v_ref_185_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(lean_object* v_namedArg_193_, lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_197_ == 0)
{
lean_object* v_name_198_; lean_object* v___x_199_; lean_object* v_name_200_; uint8_t v___x_201_; 
v_name_198_ = lean_ctor_get(v_namedArg_193_, 1);
v___x_199_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
v_name_200_ = lean_ctor_get(v___x_199_, 1);
v___x_201_ = lean_name_eq(v_name_198_, v_name_200_);
if (v___x_201_ == 0)
{
size_t v___x_202_; size_t v___x_203_; 
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_add(v_i_195_, v___x_202_);
v_i_195_ = v___x_203_;
goto _start;
}
else
{
return v___x_201_;
}
}
else
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(lean_object* v_namedArg_206_, lean_object* v_as_207_, lean_object* v_i_208_, lean_object* v_stop_209_){
_start:
{
size_t v_i_boxed_210_; size_t v_stop_boxed_211_; uint8_t v_res_212_; lean_object* v_r_213_; 
v_i_boxed_210_ = lean_unbox_usize(v_i_208_);
lean_dec(v_i_208_);
v_stop_boxed_211_ = lean_unbox_usize(v_stop_209_);
lean_dec(v_stop_209_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_206_, v_as_207_, v_i_boxed_210_, v_stop_boxed_211_);
lean_dec_ref(v_as_207_);
lean_dec_ref(v_namedArg_206_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__0));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__2));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* v_namedArgs_220_, lean_object* v_namedArg_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_array_get_size(v_namedArgs_220_);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
goto v___jp_227_;
}
else
{
if (v___x_232_ == 0)
{
goto v___jp_227_;
}
else
{
size_t v___x_233_; size_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = ((size_t)0ULL);
v___x_234_ = lean_usize_of_nat(v___x_231_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_221_, v_namedArgs_220_, v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
goto v___jp_227_;
}
else
{
lean_object* v_ref_236_; lean_object* v_name_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_namedArgs_220_);
v_ref_236_ = lean_ctor_get(v_namedArg_221_, 0);
lean_inc(v_ref_236_);
v_name_237_ = lean_ctor_get(v_namedArg_221_, 1);
lean_inc(v_name_237_);
lean_dec_ref(v_namedArg_221_);
v___x_238_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__1, &l_Lean_Elab_Term_addNamedArg___closed__1_once, _init_l_Lean_Elab_Term_addNamedArg___closed__1);
v___x_239_ = l_Lean_MessageData_ofName(v_name_237_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__3, &l_Lean_Elab_Term_addNamedArg___closed__3_once, _init_l_Lean_Elab_Term_addNamedArg___closed__3);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_236_, v___x_242_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_ref_236_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
v___jp_227_:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_array_push(v_namedArgs_220_, v_namedArg_221_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* v_namedArgs_252_, lean_object* v_namedArg_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Term_addNamedArg(v_namedArgs_252_, v_namedArg_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_object* v_00_u03b1_260_, lean_object* v_ref_261_, lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_261_, v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(lean_object* v_00_u03b1_269_, lean_object* v_ref_270_, lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(v_00_u03b1_269_, v_ref_270_, v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v_ref_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_object* v_00_u03b1_278_, lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(lean_object* v_00_u03b1_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(v_00_u03b1_286_, v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(lean_object* v_as_312_, size_t v_i_313_, size_t v_stop_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_a_322_; uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_313_, v_stop_314_);
if (v___x_326_ == 0)
{
lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_368_; 
v_fst_327_ = lean_ctor_get(v_b_315_, 0);
v_snd_328_ = lean_ctor_get(v_b_315_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_b_315_);
if (v_isSharedCheck_368_ == 0)
{
v___x_330_ = v_b_315_;
v_isShared_331_ = v_isSharedCheck_368_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_snd_328_);
lean_inc(v_fst_327_);
lean_dec(v_b_315_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_368_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_332_ = lean_array_uget_borrowed(v_as_312_, v_i_313_);
lean_inc(v___x_332_);
v___x_333_ = l_Lean_Syntax_getKind(v___x_332_);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4));
v___x_335_ = lean_name_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
v___x_337_ = lean_name_eq(v___x_333_, v___x_336_);
lean_dec(v___x_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_inc(v___x_332_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_332_);
v___x_339_ = lean_array_push(v_snd_328_, v___x_338_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_339_);
v___x_341_ = v___x_330_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_fst_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v_a_322_ = v___x_341_;
goto v___jp_321_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_330_);
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
v___x_343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8);
v___x_344_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v___x_332_, v___x_343_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v_a_322_ = v_a_345_;
goto v___jp_321_;
}
else
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_name_349_; lean_object* v___x_350_; lean_object* v_val_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_333_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = l_Lean_Syntax_getArg(v___x_332_, v___x_346_);
v___x_348_ = l_Lean_Syntax_getId(v___x_347_);
lean_dec(v___x_347_);
v_name_349_ = l_Lean_Name_eraseMacroScopes(v___x_348_);
lean_dec(v___x_348_);
v___x_350_ = lean_unsigned_to_nat(3u);
v_val_351_ = l_Lean_Syntax_getArg(v___x_332_, v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_val_351_);
v___x_353_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_332_);
v___x_354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_354_, 0, v___x_332_);
lean_ctor_set(v___x_354_, 1, v_name_349_);
lean_ctor_set(v___x_354_, 2, v___x_352_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
v___x_355_ = l_Lean_Elab_Term_addNamedArg(v_fst_327_, v___x_354_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v_a_356_);
v___x_358_ = v___x_330_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_356_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_snd_328_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v_a_322_ = v___x_358_;
goto v___jp_321_;
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_del_object(v___x_330_);
lean_dec(v_snd_328_);
v_a_360_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_355_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_355_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_b_315_);
return v___x_369_;
}
v___jp_321_:
{
size_t v___x_323_; size_t v___x_324_; 
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_313_, v___x_323_);
v_i_313_ = v___x_324_;
v_b_315_ = v_a_322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(lean_object* v_as_370_, lean_object* v_i_371_, lean_object* v_stop_372_, lean_object* v_b_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
size_t v_i_boxed_379_; size_t v_stop_boxed_380_; lean_object* v_res_381_; 
v_i_boxed_379_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_stop_boxed_380_ = lean_unbox_usize(v_stop_372_);
lean_dec(v_stop_372_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_370_, v_i_boxed_379_, v_stop_boxed_380_, v_b_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec_ref(v_as_370_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs(lean_object* v_args_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
uint8_t v___y_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; uint8_t v___y_401_; lean_object* v___y_402_; lean_object* v_fst_415_; uint8_t v_snd_416_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_array_get_size(v_args_386_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_nat_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_432_ = lean_box(0);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_sub(v___x_429_, v___x_433_);
v___x_435_ = lean_array_get_borrowed(v___x_432_, v_args_386_, v___x_434_);
lean_dec(v___x_434_);
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
lean_inc(v___x_435_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
v_fst_415_ = v_args_386_;
v_snd_416_ = v___x_437_;
goto v___jp_414_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = lean_array_pop(v_args_386_);
v_fst_415_ = v___x_438_;
v_snd_416_ = v___x_437_;
goto v___jp_414_;
}
}
else
{
uint8_t v___x_439_; 
v___x_439_ = 0;
v_fst_415_ = v_args_386_;
v_snd_416_ = v___x_439_;
goto v___jp_414_;
}
v___jp_392_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_box(v___y_393_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_snd_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_fst_394_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
v___jp_400_:
{
if (lean_obj_tag(v___y_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_fst_404_; lean_object* v_snd_405_; 
v_a_403_ = lean_ctor_get(v___y_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___y_402_, 1);
v_fst_404_ = lean_ctor_get(v_a_403_, 0);
lean_inc(v_fst_404_);
v_snd_405_ = lean_ctor_get(v_a_403_, 1);
lean_inc(v_snd_405_);
lean_dec(v_a_403_);
v___y_393_ = v___y_401_;
v_fst_394_ = v_fst_404_;
v_snd_395_ = v_snd_405_;
goto v___jp_392_;
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_a_406_ = lean_ctor_get(v___y_402_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___y_402_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___y_402_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___y_402_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
v___jp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__0));
v___x_419_ = lean_array_get_size(v_fst_415_);
v___x_420_ = lean_nat_dec_lt(v___x_417_, v___x_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v_fst_415_);
v___y_393_ = v_snd_416_;
v_fst_394_ = v___x_418_;
v_snd_395_ = v___x_418_;
goto v___jp_392_;
}
else
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__1));
v___x_422_ = lean_nat_dec_le(v___x_419_, v___x_419_);
if (v___x_422_ == 0)
{
if (v___x_420_ == 0)
{
lean_dec_ref(v_fst_415_);
v___y_393_ = v_snd_416_;
v_fst_394_ = v___x_418_;
v_snd_395_ = v___x_418_;
goto v___jp_392_;
}
else
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_419_);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_415_, v___x_423_, v___x_424_, v___x_421_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec_ref(v_fst_415_);
v___y_401_ = v_snd_416_;
v___y_402_ = v___x_425_;
goto v___jp_400_;
}
}
else
{
size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((size_t)0ULL);
v___x_427_ = lean_usize_of_nat(v___x_419_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_415_, v___x_426_, v___x_427_, v___x_421_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec_ref(v_fst_415_);
v___y_401_ = v_snd_416_;
v___y_402_ = v___x_428_;
goto v___jp_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object* v_args_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Elab_Term_expandArgs(v_args_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp(lean_object* v_stx_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = l_Lean_Syntax_getArg(v_stx_447_, v___x_453_);
v___x_455_ = l_Lean_Syntax_getArgs(v___x_454_);
lean_dec(v___x_454_);
v___x_456_ = l_Lean_Elab_Term_expandArgs(v___x_455_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_467_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_Lean_Syntax_getArg(v_stx_447_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v_a_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_463_);
v___x_465_ = v___x_459_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_a_468_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_456_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_456_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* v_stx_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Term_expandApp(v_stx_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_stx_476_);
return v_res_482_;
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
