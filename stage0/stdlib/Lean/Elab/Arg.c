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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Term_Arg_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_val_7_);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_10_; 
v_val_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_val_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_val_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Term_Arg_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim___redArg(lean_object* v_t_23_, lean_object* v_stx_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_23_, v_stx_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_stx_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_stx_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_27_, v_stx_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim___redArg(lean_object* v_t_31_, lean_object* v_expr_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_31_, v_expr_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Arg_expr_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_expr_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Term_Arg_ctorElim___redArg(v_t_35_, v_expr_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringArg___lam__0(lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_val_44_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_x_43_, 1);
v___x_45_ = lean_box(0);
v___x_46_ = 0;
v___x_47_ = l_Lean_Syntax_formatStx(v_val_44_, v___x_45_, v___x_46_);
v___x_48_ = l_Std_Format_defWidth;
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Std_Format_pretty(v___x_47_, v___x_48_, v___x_49_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_52_; 
v_val_51_ = lean_ctor_get(v_x_43_, 0);
lean_inc_ref(v_val_51_);
lean_dec_ref_known(v_x_43_, 1);
v___x_52_ = lean_expr_dbg_to_string(v_val_51_);
lean_dec_ref(v_val_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataArg___lam__0(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_val_56_; lean_object* v___x_57_; 
v_val_56_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v_x_55_, 1);
v___x_57_ = l_Lean_MessageData_ofSyntax(v_val_56_);
return v___x_57_;
}
else
{
lean_object* v_val_58_; lean_object* v___x_59_; 
v_val_58_ = lean_ctor_get(v_x_55_, 0);
lean_inc_ref(v_val_58_);
lean_dec_ref_known(v_x_55_, 1);
v___x_59_ = l_Lean_MessageData_ofExpr(v_val_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringNamedArg___lam__0(lean_object* v_s_72_){
_start:
{
lean_object* v_name_73_; lean_object* v_val_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___y_82_; 
v_name_73_ = lean_ctor_get(v_s_72_, 1);
lean_inc(v_name_73_);
v_val_74_ = lean_ctor_get(v_s_72_, 2);
lean_inc_ref(v_val_74_);
lean_dec_ref(v_s_72_);
v___x_75_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0));
v___x_76_ = 1;
v___x_77_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_73_, v___x_76_);
v___x_78_ = lean_string_append(v___x_75_, v___x_77_);
lean_dec_ref(v___x_77_);
v___x_79_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1));
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
if (lean_obj_tag(v_val_74_) == 0)
{
lean_object* v_val_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_val_86_ = lean_ctor_get(v_val_74_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v_val_74_, 1);
v___x_87_ = lean_box(0);
v___x_88_ = 0;
v___x_89_ = l_Lean_Syntax_formatStx(v_val_86_, v___x_87_, v___x_88_);
v___x_90_ = l_Std_Format_defWidth;
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_Std_Format_pretty(v___x_89_, v___x_90_, v___x_91_, v___x_91_);
v___y_82_ = v___x_92_;
goto v___jp_81_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
v_val_93_ = lean_ctor_get(v_val_74_, 0);
lean_inc_ref(v_val_93_);
lean_dec_ref_known(v_val_74_, 1);
v___x_94_ = lean_expr_dbg_to_string(v_val_93_);
lean_dec_ref(v_val_93_);
v___y_82_ = v___x_94_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_string_append(v___x_80_, v___y_82_);
lean_dec_ref(v___y_82_);
v___x_84_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2));
v___x_85_ = lean_string_append(v___x_83_, v___x_84_);
return v___x_85_;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__0));
v___x_98_ = l_Lean_stringToMessageData(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__1));
v___x_100_ = l_Lean_stringToMessageData(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Elab_Term_instToStringNamedArg___lam__0___closed__2));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0(lean_object* v_s_103_){
_start:
{
lean_object* v_name_104_; lean_object* v_val_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___y_112_; 
v_name_104_ = lean_ctor_get(v_s_103_, 1);
lean_inc(v_name_104_);
v_val_105_ = lean_ctor_get(v_s_103_, 2);
lean_inc_ref(v_val_105_);
lean_dec_ref(v_s_103_);
v___x_106_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__0);
v___x_107_ = l_Lean_MessageData_ofName(v_name_104_);
v___x_108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__1);
v___x_110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
if (lean_obj_tag(v_val_105_) == 0)
{
lean_object* v_val_116_; lean_object* v___x_117_; 
v_val_116_ = lean_ctor_get(v_val_105_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v_val_105_, 1);
v___x_117_ = l_Lean_MessageData_ofSyntax(v_val_116_);
v___y_112_ = v___x_117_;
goto v___jp_111_;
}
else
{
lean_object* v_val_118_; lean_object* v___x_119_; 
v_val_118_ = lean_ctor_get(v_val_105_, 0);
lean_inc_ref(v_val_118_);
lean_dec_ref_known(v_val_105_, 1);
v___x_119_ = l_Lean_MessageData_ofExpr(v_val_118_);
v___y_112_ = v___x_119_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_110_);
lean_ctor_set(v___x_113_, 1, v___y_112_);
v___x_114_ = lean_obj_once(&l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2, &l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2_once, _init_l_Lean_Elab_Term_instToMessageDataNamedArg___lam__0___closed__2);
v___x_115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(lean_object* v_msgData_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; lean_object* v_env_129_; uint8_t v___x_130_; lean_object* v_env_131_; lean_object* v___x_132_; lean_object* v_toCold_133_; lean_object* v_mctx_134_; lean_object* v_lctx_135_; lean_object* v_options_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_128_ = lean_st_ref_get(v___y_126_);
v_env_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc_ref(v_env_129_);
lean_dec(v___x_128_);
v___x_130_ = 0;
v_env_131_ = l_Lean_Environment_setRecordingDeps(v_env_129_, v___x_130_);
v___x_132_ = lean_st_ref_get(v___y_124_);
v_toCold_133_ = lean_ctor_get(v___y_125_, 0);
v_mctx_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_mctx_134_);
lean_dec(v___x_132_);
v_lctx_135_ = lean_ctor_get(v___y_123_, 2);
v_options_136_ = lean_ctor_get(v_toCold_133_, 2);
lean_inc_ref(v_options_136_);
lean_inc_ref(v_lctx_135_);
v___x_137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_137_, 0, v_env_131_);
lean_ctor_set(v___x_137_, 1, v_mctx_134_);
lean_ctor_set(v___x_137_, 2, v_lctx_135_);
lean_ctor_set(v___x_137_, 3, v_options_136_);
v___x_138_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_msgData_122_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_122_ = stack[0].m_obj;
lean_object* v___y_123_ = stack[1].m_obj;
lean_object* v___y_124_ = stack[2].m_obj;
lean_object* v___y_125_ = stack[3].m_obj;
lean_object* v___y_126_ = stack[4].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msgData_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msgData_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_ref_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_ref_154_ = lean_ctor_get(v___y_151_, 2);
v___x_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_spec__2(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_ref_154_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_ref_154_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_148_ = stack[0].m_obj;
lean_object* v___y_149_ = stack[1].m_obj;
lean_object* v___y_150_ = stack[2].m_obj;
lean_object* v___y_151_ = stack[3].m_obj;
lean_object* v___y_152_ = stack[4].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg___boxed(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(lean_object* v_ref_173_, lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_toCold_180_; lean_object* v_currRecDepth_181_; lean_object* v_ref_182_; uint16_t v_optionFlags_183_; uint8_t v_suppressElabErrors_184_; uint8_t v_isRecordingDeps_185_; lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_toCold_180_ = lean_ctor_get(v___y_177_, 0);
v_currRecDepth_181_ = lean_ctor_get(v___y_177_, 1);
v_ref_182_ = lean_ctor_get(v___y_177_, 2);
v_optionFlags_183_ = lean_ctor_get_uint16(v___y_177_, sizeof(void*)*3);
v_suppressElabErrors_184_ = lean_ctor_get_uint8(v___y_177_, sizeof(void*)*3 + 2);
v_isRecordingDeps_185_ = lean_ctor_get_uint8(v___y_177_, sizeof(void*)*3 + 3);
v_ref_186_ = l_Lean_replaceRef(v_ref_173_, v_ref_182_);
lean_inc(v_currRecDepth_181_);
lean_inc_ref(v_toCold_180_);
v___x_187_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_187_, 0, v_toCold_180_);
lean_ctor_set(v___x_187_, 1, v_currRecDepth_181_);
lean_ctor_set(v___x_187_, 2, v_ref_186_);
lean_ctor_set_uint16(v___x_187_, sizeof(void*)*3, v_optionFlags_183_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*3 + 2, v_suppressElabErrors_184_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*3 + 3, v_isRecordingDeps_185_);
v___x_188_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_174_, v___y_175_, v___y_176_, v___x_187_, v___y_178_);
lean_dec_ref_known(v___x_187_, 3);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_173_ = stack[0].m_obj;
lean_object* v_msg_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v___y_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v___y_178_ = stack[5].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_173_, v_msg_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg___boxed(lean_object* v_ref_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_190_, v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v_ref_190_);
return v_res_197_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(lean_object* v_namedArg_198_, lean_object* v_as_199_, size_t v_i_200_, size_t v_stop_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_eq(v_i_200_, v_stop_201_);
if (v___x_202_ == 0)
{
lean_object* v_name_203_; lean_object* v___x_204_; lean_object* v_name_205_; uint8_t v___x_206_; 
v_name_203_ = lean_ctor_get(v_namedArg_198_, 1);
v___x_204_ = lean_array_uget_borrowed(v_as_199_, v_i_200_);
v_name_205_ = lean_ctor_get(v___x_204_, 1);
v___x_206_ = lean_name_eq(v_name_203_, v_name_205_);
if (v___x_206_ == 0)
{
size_t v___x_207_; size_t v___x_208_; 
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_add(v_i_200_, v___x_207_);
v_i_200_ = v___x_208_;
goto _start;
}
else
{
return v___x_206_;
}
}
else
{
uint8_t v___x_210_; 
v___x_210_ = 0;
return v___x_210_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_namedArg_198_ = stack[0].m_obj;
lean_object* v_as_199_ = stack[1].m_obj;
size_t v_i_200_ = stack[2].m_num;
size_t v_stop_201_ = stack[3].m_num;
uint8_t v_res_211_;
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_198_, v_as_199_, v_i_200_, v_stop_201_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0___boxed(lean_object* v_namedArg_212_, lean_object* v_as_213_, lean_object* v_i_214_, lean_object* v_stop_215_){
_start:
{
size_t v_i_boxed_216_; size_t v_stop_boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v_i_boxed_216_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_stop_boxed_217_ = lean_unbox_usize(v_stop_215_);
lean_dec(v_stop_215_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_212_, v_as_213_, v_i_boxed_216_, v_stop_boxed_217_);
lean_dec_ref(v_as_213_);
lean_dec_ref(v_namedArg_212_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__0));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Term_addNamedArg___closed__2));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* v_namedArgs_226_, lean_object* v_namedArg_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_array_get_size(v_namedArgs_226_);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
goto v___jp_233_;
}
else
{
if (v___x_238_ == 0)
{
goto v___jp_233_;
}
else
{
size_t v___x_239_; size_t v___x_240_; uint8_t v___x_241_; 
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_237_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_addNamedArg_spec__0(v_namedArg_227_, v_namedArgs_226_, v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
goto v___jp_233_;
}
else
{
lean_object* v_ref_242_; lean_object* v_name_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v_namedArgs_226_);
v_ref_242_ = lean_ctor_get(v_namedArg_227_, 0);
lean_inc(v_ref_242_);
v_name_243_ = lean_ctor_get(v_namedArg_227_, 1);
lean_inc(v_name_243_);
lean_dec_ref(v_namedArg_227_);
v___x_244_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__1, &l_Lean_Elab_Term_addNamedArg___closed__1_once, _init_l_Lean_Elab_Term_addNamedArg___closed__1);
v___x_245_ = l_Lean_MessageData_ofName(v_name_243_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_obj_once(&l_Lean_Elab_Term_addNamedArg___closed__3, &l_Lean_Elab_Term_addNamedArg___closed__3_once, _init_l_Lean_Elab_Term_addNamedArg___closed__3);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_242_, v___x_248_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_ref_242_);
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_array_push(v_namedArgs_226_, v_namedArg_227_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_addNamedArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_namedArgs_226_ = stack[0].m_obj;
lean_object* v_namedArg_227_ = stack[1].m_obj;
lean_object* v_a_228_ = stack[2].m_obj;
lean_object* v_a_229_ = stack[3].m_obj;
lean_object* v_a_230_ = stack[4].m_obj;
lean_object* v_a_231_ = stack[5].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lean_Elab_Term_addNamedArg(v_namedArgs_226_, v_namedArg_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* v_namedArgs_259_, lean_object* v_namedArg_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Elab_Term_addNamedArg(v_namedArgs_259_, v_namedArg_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
return v_res_266_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_object* v_00_u03b1_267_, lean_object* v_ref_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v_ref_268_, v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_268_ = stack[1].m_obj;
lean_object* v_msg_269_ = stack[2].m_obj;
lean_object* v___y_270_ = stack[3].m_obj;
lean_object* v___y_271_ = stack[4].m_obj;
lean_object* v___y_272_ = stack[5].m_obj;
lean_object* v___y_273_ = stack[6].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(lean_box(0), v_ref_268_, v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___boxed(lean_object* v_00_u03b1_277_, lean_object* v_ref_278_, lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1(v_00_u03b1_277_, v_ref_278_, v_msg_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_ref_278_);
return v_res_285_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_object* v_00_u03b1_286_, lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___redArg(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_287_ = stack[1].m_obj;
lean_object* v___y_288_ = stack[2].m_obj;
lean_object* v___y_289_ = stack[3].m_obj;
lean_object* v___y_290_ = stack[4].m_obj;
lean_object* v___y_291_ = stack[5].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(lean_box(0), v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1___boxed(lean_object* v_00_u03b1_295_, lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1_spec__1(v_00_u03b1_295_, v_msg_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__7));
v___x_320_ = l_Lean_stringToMessageData(v___x_319_);
return v___x_320_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(lean_object* v_as_321_, size_t v_i_322_, size_t v_stop_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_a_331_; uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_eq(v_i_322_, v_stop_323_);
if (v___x_335_ == 0)
{
lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_377_; 
v_fst_336_ = lean_ctor_get(v_b_324_, 0);
v_snd_337_ = lean_ctor_get(v_b_324_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_377_ == 0)
{
v___x_339_ = v_b_324_;
v_isShared_340_ = v_isSharedCheck_377_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_inc(v_fst_336_);
lean_dec(v_b_324_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_377_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_341_ = lean_array_uget_borrowed(v_as_321_, v_i_322_);
lean_inc(v___x_341_);
v___x_342_ = l_Lean_Syntax_getKind(v___x_341_);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__4));
v___x_344_ = lean_name_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
v___x_346_ = lean_name_eq(v___x_342_, v___x_345_);
lean_dec(v___x_342_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_inc(v___x_341_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_341_);
v___x_348_ = lean_array_push(v_snd_337_, v___x_347_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_348_);
v___x_350_ = v___x_339_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_fst_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v_a_331_ = v___x_350_;
goto v___jp_330_;
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_del_object(v___x_339_);
lean_dec(v_snd_337_);
lean_dec(v_fst_336_);
v___x_352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__8);
v___x_353_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_addNamedArg_spec__1___redArg(v___x_341_, v___x_352_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v_a_331_ = v_a_354_;
goto v___jp_330_;
}
else
{
return v___x_353_;
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_name_358_; lean_object* v___x_359_; lean_object* v_val_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v___x_342_);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = l_Lean_Syntax_getArg(v___x_341_, v___x_355_);
v___x_357_ = l_Lean_Syntax_getId(v___x_356_);
lean_dec(v___x_356_);
v_name_358_ = l_Lean_Name_eraseMacroScopes(v___x_357_);
lean_dec(v___x_357_);
v___x_359_ = lean_unsigned_to_nat(3u);
v_val_360_ = l_Lean_Syntax_getArg(v___x_341_, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v_val_360_);
v___x_362_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_341_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v___x_341_);
lean_ctor_set(v___x_363_, 1, v_name_358_);
lean_ctor_set(v___x_363_, 2, v___x_361_);
lean_ctor_set(v___x_363_, 3, v___x_362_);
v___x_364_ = l_Lean_Elab_Term_addNamedArg(v_fst_336_, v___x_363_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_a_365_);
v___x_367_ = v___x_339_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_365_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_snd_337_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v_a_331_ = v___x_367_;
goto v___jp_330_;
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_339_);
lean_dec(v_snd_337_);
v_a_369_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_364_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_364_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_b_324_);
return v___x_378_;
}
v___jp_330_:
{
size_t v___x_332_; size_t v___x_333_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_322_, v___x_332_);
v_i_322_ = v___x_333_;
v_b_324_ = v_a_331_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_321_ = stack[0].m_obj;
size_t v_i_322_ = stack[1].m_num;
size_t v_stop_323_ = stack[2].m_num;
lean_object* v_b_324_ = stack[3].m_obj;
lean_object* v___y_325_ = stack[4].m_obj;
lean_object* v___y_326_ = stack[5].m_obj;
lean_object* v___y_327_ = stack[6].m_obj;
lean_object* v___y_328_ = stack[7].m_obj;
lean_object* v_res_379_;
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_321_, v_i_322_, v_stop_323_, v_b_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___boxed(lean_object* v_as_380_, lean_object* v_i_381_, lean_object* v_stop_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_382_);
lean_dec(v_stop_382_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_as_380_, v_i_boxed_389_, v_stop_boxed_390_, v_b_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_as_380_);
return v_res_391_;
}
}
lean_object* l_Lean_Elab_Term_expandArgs(lean_object* v_args_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
uint8_t v___y_403_; lean_object* v_fst_404_; lean_object* v_snd_405_; uint8_t v___y_411_; lean_object* v___y_412_; lean_object* v_fst_425_; uint8_t v_snd_426_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_array_get_size(v_args_396_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_nat_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_sub(v___x_439_, v___x_443_);
v___x_445_ = lean_array_get_borrowed(v___x_442_, v_args_396_, v___x_444_);
lean_dec(v___x_444_);
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0___closed__6));
lean_inc(v___x_445_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
v_fst_425_ = v_args_396_;
v_snd_426_ = v___x_447_;
goto v___jp_424_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_array_pop(v_args_396_);
v_fst_425_ = v___x_448_;
v_snd_426_ = v___x_447_;
goto v___jp_424_;
}
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 0;
v_fst_425_ = v_args_396_;
v_snd_426_ = v___x_449_;
goto v___jp_424_;
}
v___jp_402_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_box(v___y_403_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_snd_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_fst_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
v___jp_410_:
{
if (lean_obj_tag(v___y_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; 
v_a_413_ = lean_ctor_get(v___y_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___y_412_, 1);
v_fst_414_ = lean_ctor_get(v_a_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v_a_413_, 1);
lean_inc(v_snd_415_);
lean_dec(v_a_413_);
v___y_403_ = v___y_411_;
v_fst_404_ = v_fst_414_;
v_snd_405_ = v_snd_415_;
goto v___jp_402_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___y_412_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___y_412_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___y_412_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___y_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
v___jp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__0));
v___x_429_ = lean_array_get_size(v_fst_425_);
v___x_430_ = lean_nat_dec_lt(v___x_427_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec_ref(v_fst_425_);
v___y_403_ = v_snd_426_;
v_fst_404_ = v___x_428_;
v_snd_405_ = v___x_428_;
goto v___jp_402_;
}
else
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Elab_Term_expandArgs___closed__1));
v___x_432_ = lean_nat_dec_le(v___x_429_, v___x_429_);
if (v___x_432_ == 0)
{
if (v___x_430_ == 0)
{
lean_dec_ref(v_fst_425_);
v___y_403_ = v_snd_426_;
v_fst_404_ = v___x_428_;
v_snd_405_ = v___x_428_;
goto v___jp_402_;
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_of_nat(v___x_429_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_425_, v___x_433_, v___x_434_, v___x_431_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec_ref(v_fst_425_);
v___y_411_ = v_snd_426_;
v___y_412_ = v___x_435_;
goto v___jp_410_;
}
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_429_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_expandArgs_spec__0(v_fst_425_, v___x_436_, v___x_437_, v___x_431_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec_ref(v_fst_425_);
v___y_411_ = v_snd_426_;
v___y_412_ = v___x_438_;
goto v___jp_410_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_expandArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_396_ = stack[0].m_obj;
lean_object* v_a_397_ = stack[1].m_obj;
lean_object* v_a_398_ = stack[2].m_obj;
lean_object* v_a_399_ = stack[3].m_obj;
lean_object* v_a_400_ = stack[4].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_Elab_Term_expandArgs(v_args_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object* v_args_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Elab_Term_expandArgs(v_args_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
return v_res_457_;
}
}
lean_object* l_Lean_Elab_Term_expandApp(lean_object* v_stx_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_464_);
v___x_466_ = l_Lean_Syntax_getArgs(v___x_465_);
lean_dec(v___x_465_);
v___x_467_ = l_Lean_Elab_Term_expandArgs(v___x_466_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_478_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_a_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_474_);
v___x_476_ = v___x_470_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_467_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_467_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_expandApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_458_ = stack[0].m_obj;
lean_object* v_a_459_ = stack[1].m_obj;
lean_object* v_a_460_ = stack[2].m_obj;
lean_object* v_a_461_ = stack[3].m_obj;
lean_object* v_a_462_ = stack[4].m_obj;
lean_object* v_res_487_;
v_res_487_ = l_Lean_Elab_Term_expandApp(v_stx_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* v_stx_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_Term_expandApp(v_stx_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_stx_488_);
return v_res_494_;
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
