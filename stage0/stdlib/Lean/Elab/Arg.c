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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_instInhabitedArg_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg_default = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instInhabitedNamedArg = (const lean_object*)&l_Lean_Elab_Term_instInhabitedNamedArg_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Term_instToMessageDataArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instToMessageDataArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_instToMessageDataArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Term_instToMessageDataArg = (const lean_object*)&l_Lean_Elab_Term_instToMessageDataArg___closed__0_value;
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
static lean_once_cell_t l_Lean_Elab_Term_expandArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_expandArgs___closed__1;
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
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_val_8_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; 
v_val_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_val_10_);
lean_dec_ref(v_t_6_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataArg___lam__0(lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_val_52_; lean_object* v___x_53_; 
v_val_52_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_52_);
lean_dec_ref(v_x_51_);
v___x_53_ = l_Lean_MessageData_ofSyntax(v_val_52_);
return v___x_53_;
}
else
{
lean_object* v_val_54_; lean_object* v___x_55_; 
v_val_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc_ref(v_val_54_);
lean_dec_ref(v_x_51_);
v___x_55_ = l_Lean_MessageData_ofExpr(v_val_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(lean_object* v_msgData_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_env_65_; lean_object* v___x_66_; lean_object* v_mctx_67_; lean_object* v_lctx_68_; lean_object* v_options_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_64_ = lean_st_ref_get(v___y_62_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = lean_st_ref_get(v___y_60_);
v_mctx_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_mctx_67_);
lean_dec(v___x_66_);
v_lctx_68_ = lean_ctor_get(v___y_59_, 2);
v_options_69_ = lean_ctor_get(v___y_61_, 2);
lean_inc_ref(v_options_69_);
lean_inc_ref(v_lctx_68_);
v___x_70_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_70_, 0, v_env_65_);
lean_ctor_set(v___x_70_, 1, v_mctx_67_);
lean_ctor_set(v___x_70_, 2, v_lctx_68_);
lean_ctor_set(v___x_70_, 3, v_options_69_);
v___x_71_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_msgData_58_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msgData_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_ref_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_ref_86_ = lean_ctor_get(v___y_83_, 5);
v___x_87_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_inc(v_ref_86_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_ref_86_);
lean_ctor_set(v___x_92_, 1, v_a_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg___boxed(lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(lean_object* v_ref_104_, lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_fileName_111_; lean_object* v_fileMap_112_; lean_object* v_options_113_; lean_object* v_currRecDepth_114_; lean_object* v_maxRecDepth_115_; lean_object* v_ref_116_; lean_object* v_currNamespace_117_; lean_object* v_openDecls_118_; lean_object* v_initHeartbeats_119_; lean_object* v_maxHeartbeats_120_; lean_object* v_quotContext_121_; lean_object* v_currMacroScope_122_; uint8_t v_diag_123_; lean_object* v_cancelTk_x3f_124_; uint8_t v_suppressElabErrors_125_; lean_object* v_inheritedTraceOptions_126_; lean_object* v_ref_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_fileName_111_ = lean_ctor_get(v___y_108_, 0);
v_fileMap_112_ = lean_ctor_get(v___y_108_, 1);
v_options_113_ = lean_ctor_get(v___y_108_, 2);
v_currRecDepth_114_ = lean_ctor_get(v___y_108_, 3);
v_maxRecDepth_115_ = lean_ctor_get(v___y_108_, 4);
v_ref_116_ = lean_ctor_get(v___y_108_, 5);
v_currNamespace_117_ = lean_ctor_get(v___y_108_, 6);
v_openDecls_118_ = lean_ctor_get(v___y_108_, 7);
v_initHeartbeats_119_ = lean_ctor_get(v___y_108_, 8);
v_maxHeartbeats_120_ = lean_ctor_get(v___y_108_, 9);
v_quotContext_121_ = lean_ctor_get(v___y_108_, 10);
v_currMacroScope_122_ = lean_ctor_get(v___y_108_, 11);
v_diag_123_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*14);
v_cancelTk_x3f_124_ = lean_ctor_get(v___y_108_, 12);
v_suppressElabErrors_125_ = lean_ctor_get_uint8(v___y_108_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_126_ = lean_ctor_get(v___y_108_, 13);
v_ref_127_ = l_Lean_replaceRef(v_ref_104_, v_ref_116_);
lean_inc_ref(v_inheritedTraceOptions_126_);
lean_inc(v_cancelTk_x3f_124_);
lean_inc(v_currMacroScope_122_);
lean_inc(v_quotContext_121_);
lean_inc(v_maxHeartbeats_120_);
lean_inc(v_initHeartbeats_119_);
lean_inc(v_openDecls_118_);
lean_inc(v_currNamespace_117_);
lean_inc(v_maxRecDepth_115_);
lean_inc(v_currRecDepth_114_);
lean_inc_ref(v_options_113_);
lean_inc_ref(v_fileMap_112_);
lean_inc_ref(v_fileName_111_);
v___x_128_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_128_, 0, v_fileName_111_);
lean_ctor_set(v___x_128_, 1, v_fileMap_112_);
lean_ctor_set(v___x_128_, 2, v_options_113_);
lean_ctor_set(v___x_128_, 3, v_currRecDepth_114_);
lean_ctor_set(v___x_128_, 4, v_maxRecDepth_115_);
lean_ctor_set(v___x_128_, 5, v_ref_127_);
lean_ctor_set(v___x_128_, 6, v_currNamespace_117_);
lean_ctor_set(v___x_128_, 7, v_openDecls_118_);
lean_ctor_set(v___x_128_, 8, v_initHeartbeats_119_);
lean_ctor_set(v___x_128_, 9, v_maxHeartbeats_120_);
lean_ctor_set(v___x_128_, 10, v_quotContext_121_);
lean_ctor_set(v___x_128_, 11, v_currMacroScope_122_);
lean_ctor_set(v___x_128_, 12, v_cancelTk_x3f_124_);
lean_ctor_set(v___x_128_, 13, v_inheritedTraceOptions_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*14, v_diag_123_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*14 + 1, v_suppressElabErrors_125_);
v___x_129_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_105_, v___y_106_, v___y_107_, v___x_128_, v___y_109_);
lean_dec_ref(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(lean_object* v_ref_130_, lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_130_, v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v_ref_130_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(lean_object* v_namedArg_138_, lean_object* v_as_139_, size_t v_i_140_, size_t v_stop_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_eq(v_i_140_, v_stop_141_);
if (v___x_142_ == 0)
{
lean_object* v_name_143_; lean_object* v___x_144_; lean_object* v_name_145_; uint8_t v___x_146_; 
v_name_143_ = lean_ctor_get(v_namedArg_138_, 1);
v___x_144_ = lean_array_uget_borrowed(v_as_139_, v_i_140_);
v_name_145_ = lean_ctor_get(v___x_144_, 1);
v___x_146_ = lean_name_eq(v_name_143_, v_name_145_);
if (v___x_146_ == 0)
{
size_t v___x_147_; size_t v___x_148_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_140_, v___x_147_);
v_i_140_ = v___x_148_;
goto _start;
}
else
{
return v___x_146_;
}
}
else
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(lean_object* v_namedArg_151_, lean_object* v_as_152_, lean_object* v_i_153_, lean_object* v_stop_154_){
_start:
{
size_t v_i_boxed_155_; size_t v_stop_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_i_boxed_155_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_stop_boxed_156_ = lean_unbox_usize(v_stop_154_);
lean_dec(v_stop_154_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_151_, v_as_152_, v_i_boxed_155_, v_stop_boxed_156_);
lean_dec_ref(v_as_152_);
lean_dec_ref(v_namedArg_151_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__0));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__2));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* v_namedArgs_165_, lean_object* v_namedArg_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_array_get_size(v_namedArgs_165_);
v___x_177_ = lean_nat_dec_lt(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
goto v___jp_172_;
}
else
{
if (v___x_177_ == 0)
{
goto v___jp_172_;
}
else
{
size_t v___x_178_; size_t v___x_179_; uint8_t v___x_180_; 
v___x_178_ = ((size_t)0ULL);
v___x_179_ = lean_usize_of_nat(v___x_176_);
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_166_, v_namedArgs_165_, v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
goto v___jp_172_;
}
else
{
lean_object* v_ref_181_; lean_object* v_name_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref(v_namedArgs_165_);
v_ref_181_ = lean_ctor_get(v_namedArg_166_, 0);
lean_inc(v_ref_181_);
v_name_182_ = lean_ctor_get(v_namedArg_166_, 1);
lean_inc(v_name_182_);
lean_dec_ref(v_namedArg_166_);
v___x_183_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__1, &l_Lean_Elab_Term_addNamedArg___closed__1_once, _init_l_Lean_Elab_Term_addNamedArg___closed__1);
v___x_184_ = l_Lean_MessageData_ofName(v_name_182_);
v___x_185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__3, &l_Lean_Elab_Term_addNamedArg___closed__3_once, _init_l_Lean_Elab_Term_addNamedArg___closed__3);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_181_, v___x_187_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec(v_ref_181_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
v___jp_172_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_array_push(v_namedArgs_165_, v_namedArg_166_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* v_namedArgs_197_, lean_object* v_namedArg_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Elab_Term_addNamedArg(v_namedArgs_197_, v_namedArg_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_object* v_00_u03b1_205_, lean_object* v_ref_206_, lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_206_, v_msg_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(lean_object* v_00_u03b1_214_, lean_object* v_ref_215_, lean_object* v_msg_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(v_00_u03b1_214_, v_ref_215_, v_msg_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v_ref_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_object* v_00_u03b1_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(lean_object* v_00_u03b1_231_, lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(v_00_u03b1_231_, v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(lean_object* v_as_257_, size_t v_i_258_, size_t v_stop_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_a_267_; uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_eq(v_i_258_, v_stop_259_);
if (v___x_271_ == 0)
{
lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_312_; 
v_fst_272_ = lean_ctor_get(v_b_260_, 0);
v_snd_273_ = lean_ctor_get(v_b_260_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_b_260_);
if (v_isSharedCheck_312_ == 0)
{
v___x_275_ = v_b_260_;
v_isShared_276_ = v_isSharedCheck_312_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snd_273_);
lean_inc(v_fst_272_);
lean_dec(v_b_260_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_312_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_277_ = lean_array_uget_borrowed(v_as_257_, v_i_258_);
lean_inc(v___x_277_);
v___x_278_ = l_Lean_Syntax_getKind(v___x_277_);
v___x_279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4));
v___x_280_ = lean_name_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
v___x_282_ = lean_name_eq(v___x_278_, v___x_281_);
lean_dec(v___x_278_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_inc(v___x_277_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_277_);
v___x_284_ = lean_array_push(v_snd_273_, v___x_283_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_284_);
v___x_286_ = v___x_275_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_fst_272_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_a_267_ = v___x_286_;
goto v___jp_266_;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_del_object(v___x_275_);
lean_dec(v_snd_273_);
lean_dec(v_fst_272_);
v___x_288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8);
v___x_289_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v___x_277_, v___x_288_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
v_a_267_ = v_a_290_;
goto v___jp_266_;
}
else
{
return v___x_289_;
}
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_name_294_; lean_object* v___x_295_; lean_object* v_val_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___x_278_);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = l_Lean_Syntax_getArg(v___x_277_, v___x_291_);
v___x_293_ = l_Lean_Syntax_getId(v___x_292_);
lean_dec(v___x_292_);
v_name_294_ = lean_erase_macro_scopes(v___x_293_);
v___x_295_ = lean_unsigned_to_nat(3u);
v_val_296_ = l_Lean_Syntax_getArg(v___x_277_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v_val_296_);
lean_inc(v___x_277_);
v___x_298_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_298_, 0, v___x_277_);
lean_ctor_set(v___x_298_, 1, v_name_294_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*3, v___x_271_);
v___x_299_ = l_Lean_Elab_Term_addNamedArg(v_fst_272_, v___x_298_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_a_300_);
v___x_302_ = v___x_275_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_snd_273_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v_a_267_ = v___x_302_;
goto v___jp_266_;
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_275_);
lean_dec(v_snd_273_);
v_a_304_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_299_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_299_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v_b_260_);
return v___x_313_;
}
v___jp_266_:
{
size_t v___x_268_; size_t v___x_269_; 
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_258_, v___x_268_);
v_i_258_ = v___x_269_;
v_b_260_ = v_a_267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(lean_object* v_as_314_, lean_object* v_i_315_, lean_object* v_stop_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
size_t v_i_boxed_323_; size_t v_stop_boxed_324_; lean_object* v_res_325_; 
v_i_boxed_323_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_stop_boxed_324_ = lean_unbox_usize(v_stop_316_);
lean_dec(v_stop_316_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_314_, v_i_boxed_323_, v_stop_boxed_324_, v_b_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_as_314_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandArgs___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__0));
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs(lean_object* v_args_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
uint8_t v___y_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; uint8_t v___y_345_; lean_object* v___y_346_; lean_object* v_fst_359_; uint8_t v_snd_360_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_array_get_size(v_args_330_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_nat_dec_eq(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_sub(v___x_373_, v___x_377_);
v___x_379_ = lean_array_get_borrowed(v___x_376_, v_args_330_, v___x_378_);
lean_dec(v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
lean_inc(v___x_379_);
v___x_381_ = l_Lean_Syntax_isOfKind(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
v_fst_359_ = v_args_330_;
v_snd_360_ = v___x_381_;
goto v___jp_358_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_array_pop(v_args_330_);
v_fst_359_ = v___x_382_;
v_snd_360_ = v___x_381_;
goto v___jp_358_;
}
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 0;
v_fst_359_ = v_args_330_;
v_snd_360_ = v___x_383_;
goto v___jp_358_;
}
v___jp_336_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_box(v___y_337_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_snd_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_fst_338_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
v___jp_344_:
{
if (lean_obj_tag(v___y_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; 
v_a_347_ = lean_ctor_get(v___y_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___y_346_);
v_fst_348_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_fst_348_);
v_snd_349_ = lean_ctor_get(v_a_347_, 1);
lean_inc(v_snd_349_);
lean_dec(v_a_347_);
v___y_337_ = v___y_345_;
v_fst_338_ = v_fst_348_;
v_snd_339_ = v_snd_349_;
goto v___jp_336_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v___y_346_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___y_346_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___y_346_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___y_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
v___jp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__0));
v___x_363_ = lean_array_get_size(v_fst_359_);
v___x_364_ = lean_nat_dec_lt(v___x_361_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec_ref(v_fst_359_);
v___y_337_ = v_snd_360_;
v_fst_338_ = v___x_362_;
v_snd_339_ = v___x_362_;
goto v___jp_336_;
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Elab_Term_expandArgs___closed__1, &l_Lean_Elab_Term_expandArgs___closed__1_once, _init_l_Lean_Elab_Term_expandArgs___closed__1);
v___x_366_ = lean_nat_dec_le(v___x_363_, v___x_363_);
if (v___x_366_ == 0)
{
if (v___x_364_ == 0)
{
lean_dec_ref(v_fst_359_);
v___y_337_ = v_snd_360_;
v_fst_338_ = v___x_362_;
v_snd_339_ = v___x_362_;
goto v___jp_336_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = ((size_t)0ULL);
v___x_368_ = lean_usize_of_nat(v___x_363_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_359_, v___x_367_, v___x_368_, v___x_365_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec_ref(v_fst_359_);
v___y_345_ = v_snd_360_;
v___y_346_ = v___x_369_;
goto v___jp_344_;
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_363_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_359_, v___x_370_, v___x_371_, v___x_365_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec_ref(v_fst_359_);
v___y_345_ = v_snd_360_;
v___y_346_ = v___x_372_;
goto v___jp_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object* v_args_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_Term_expandArgs(v_args_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp(lean_object* v_stx_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = l_Lean_Syntax_getArg(v_stx_391_, v___x_397_);
v___x_399_ = l_Lean_Syntax_getArgs(v___x_398_);
lean_dec(v___x_398_);
v___x_400_ = l_Lean_Elab_Term_expandArgs(v___x_399_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_411_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_411_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = l_Lean_Syntax_getArg(v_stx_391_, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_407_);
v___x_409_ = v___x_403_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_400_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_400_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* v_stx_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_Term_expandApp(v_stx_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_stx_420_);
return v_res_426_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Arg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
