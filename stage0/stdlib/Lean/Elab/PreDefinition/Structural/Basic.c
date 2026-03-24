// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Basic
// Imports: public import Lean.Meta.ForEachExpr
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_blt___boxed(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_blt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value;
static const lean_array_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value;
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 93, 210, 117, 29, 155, 126, 189)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 202, 50, 112, 18, 212, 25, 136)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 23, 214, 102, 176, 92, 61, 7)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 242, 64, 13, 155, 86, 160, 173)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 198, 105, 72, 111, 167, 237, 39)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 69, 67, 115, 43, 149, 20, 105)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 31, 132, 210, 180, 148, 101, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 98, 226, 195, 133, 57, 212, 22)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 87, 212, 210, 179, 92, 88, 148)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2093547783) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(133, 199, 80, 82, 103, 156, 192, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 239, 117, 197, 243, 90, 72, 42)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 62, 224, 211, 204, 80, 164, 101)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(83, 62, 38, 220, 18, 160, 27, 136)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object* v_recArgPos_1_, lean_object* v_recFnName_2_, lean_object* v_e_3_){
_start:
{
uint8_t v___y_5_; uint8_t v___x_12_; 
v___x_12_ = l_Lean_Expr_isAppOf(v_e_3_, v_recFnName_2_);
if (v___x_12_ == 0)
{
v___y_5_ = v___x_12_;
goto v___jp_4_;
}
else
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = l_Lean_Expr_getAppNumArgs(v_e_3_);
v___x_14_ = lean_nat_dec_lt(v_recArgPos_1_, v___x_13_);
lean_dec(v___x_13_);
v___y_5_ = v___x_14_;
goto v___jp_4_;
}
v___jp_4_:
{
if (v___y_5_ == 0)
{
return v___y_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_6_ = l_Lean_Expr_getAppNumArgs(v_e_3_);
v___x_7_ = lean_nat_sub(v___x_6_, v_recArgPos_1_);
lean_dec(v___x_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_sub(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = l_Lean_Expr_getRevArg_x21(v_e_3_, v___x_9_);
v___x_11_ = l_Lean_Expr_hasLooseBVars(v___x_10_);
lean_dec_ref(v___x_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object* v_recArgPos_15_, lean_object* v_recFnName_16_, lean_object* v_e_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(v_recArgPos_15_, v_recFnName_16_, v_e_17_);
lean_dec_ref(v_e_17_);
lean_dec(v_recFnName_16_);
lean_dec(v_recArgPos_15_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object* v_recFnName_20_, lean_object* v_recArgPos_21_, lean_object* v_e_22_){
_start:
{
lean_object* v___f_23_; lean_object* v_app_x3f_24_; 
v___f_23_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed), 3, 2);
lean_closure_set(v___f_23_, 0, v_recArgPos_21_);
lean_closure_set(v___f_23_, 1, v_recFnName_20_);
v_app_x3f_24_ = lean_find_expr(v___f_23_, v_e_22_);
lean_dec_ref(v___f_23_);
if (lean_obj_tag(v_app_x3f_24_) == 0)
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
lean_dec_ref(v_app_x3f_24_);
v___x_26_ = 1;
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object* v_recFnName_27_, lean_object* v_recArgPos_28_, lean_object* v_e_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_recFnName_27_, v_recArgPos_28_, v_e_29_);
lean_dec_ref(v_e_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object* v_as_32_, size_t v_i_33_, size_t v_stop_34_, lean_object* v_b_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_usize_dec_eq(v_i_33_, v_stop_34_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; size_t v___x_40_; size_t v___x_41_; 
v___x_37_ = lean_array_uget_borrowed(v_as_32_, v_i_33_);
v___x_38_ = lean_array_get_size(v___x_37_);
v___x_39_ = lean_nat_add(v_b_35_, v___x_38_);
lean_dec(v_b_35_);
v___x_40_ = ((size_t)1ULL);
v___x_41_ = lean_usize_add(v_i_33_, v___x_40_);
v_i_33_ = v___x_41_;
v_b_35_ = v___x_39_;
goto _start;
}
else
{
return v_b_35_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object* v_as_43_, lean_object* v_i_44_, lean_object* v_stop_45_, lean_object* v_b_46_){
_start:
{
size_t v_i_boxed_47_; size_t v_stop_boxed_48_; lean_object* v_res_49_; 
v_i_boxed_47_ = lean_unbox_usize(v_i_44_);
lean_dec(v_i_44_);
v_stop_boxed_48_ = lean_unbox_usize(v_stop_45_);
lean_dec(v_stop_45_);
v_res_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_as_43_, v_i_boxed_47_, v_stop_boxed_48_, v_b_46_);
lean_dec_ref(v_as_43_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object* v_positions_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_array_get_size(v_positions_50_);
v___x_53_ = lean_nat_dec_lt(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
return v___x_51_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = lean_nat_dec_le(v___x_52_, v___x_52_);
if (v___x_54_ == 0)
{
if (v___x_53_ == 0)
{
return v___x_51_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_52_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_50_, v___x_55_, v___x_56_, v___x_51_);
return v___x_57_;
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_52_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_50_, v___x_58_, v___x_59_, v___x_51_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object* v_positions_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_61_);
lean_dec_ref(v_positions_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object* v_inst_63_, lean_object* v_xs_64_, lean_object* v_f_65_, lean_object* v_inst_66_, lean_object* v_x_67_, lean_object* v_x1_68_, lean_object* v_x2_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_70_ = lean_array_get_borrowed(v_inst_63_, v_xs_64_, v_x2_69_);
lean_inc(v___x_70_);
v___x_71_ = lean_apply_1(v_f_65_, v___x_70_);
v___x_72_ = lean_apply_2(v_inst_66_, v___x_71_, v_x_67_);
v___x_73_ = lean_unbox(v___x_72_);
if (v___x_73_ == 0)
{
lean_dec(v_x2_69_);
return v_x1_68_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_array_push(v_x1_68_, v_x2_69_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object* v_inst_75_, lean_object* v_xs_76_, lean_object* v_f_77_, lean_object* v_inst_78_, lean_object* v_x_79_, lean_object* v_x1_80_, lean_object* v_x2_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(v_inst_75_, v_xs_76_, v_f_77_, v_inst_78_, v_x_79_, v_x1_80_, v_x2_81_);
lean_dec_ref(v_xs_76_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object* v_xs_104_, lean_object* v_inst_105_, lean_object* v_f_106_, lean_object* v_inst_107_, lean_object* v_x_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_109_ = lean_array_get_size(v_xs_104_);
v___x_110_ = l_Array_range(v___x_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_array_get_size(v___x_110_);
v___x_113_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0));
v___x_114_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v___x_115_ = lean_nat_dec_lt(v___x_111_, v___x_112_);
if (v___x_115_ == 0)
{
lean_dec_ref(v___x_110_);
lean_dec(v_x_108_);
lean_dec_ref(v_inst_107_);
lean_dec(v_f_106_);
lean_dec(v_inst_105_);
lean_dec_ref(v_xs_104_);
return v___x_113_;
}
else
{
lean_object* v___f_116_; uint8_t v___x_117_; 
v___f_116_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_116_, 0, v_inst_105_);
lean_closure_set(v___f_116_, 1, v_xs_104_);
lean_closure_set(v___f_116_, 2, v_f_106_);
lean_closure_set(v___f_116_, 3, v_inst_107_);
lean_closure_set(v___f_116_, 4, v_x_108_);
v___x_117_ = lean_nat_dec_le(v___x_112_, v___x_112_);
if (v___x_117_ == 0)
{
if (v___x_115_ == 0)
{
lean_dec_ref(v___f_116_);
lean_dec_ref(v___x_110_);
return v___x_113_;
}
else
{
size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; 
v___x_118_ = ((size_t)0ULL);
v___x_119_ = lean_usize_of_nat(v___x_112_);
v___x_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_114_, v___f_116_, v___x_110_, v___x_118_, v___x_119_, v___x_113_);
return v___x_120_;
}
}
else
{
size_t v___x_121_; size_t v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((size_t)0ULL);
v___x_122_ = lean_usize_of_nat(v___x_112_);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_114_, v___f_116_, v___x_110_, v___x_121_, v___x_122_, v___x_113_);
return v___x_123_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Array_instInhabited(lean_box(0));
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3));
v___x_129_ = lean_unsigned_to_nat(2u);
v___x_130_ = lean_unsigned_to_nat(63u);
v___x_131_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
v___x_132_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_133_ = l_mkPanicMessageWithDecl(v___x_132_, v___x_131_, v___x_130_, v___x_129_, v___x_128_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_f_141_, lean_object* v_xs_142_, lean_object* v_ys_143_){
_start:
{
lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; size_t v_sz_151_; size_t v___x_152_; lean_object* v_positions_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___y_157_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_177_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___f_148_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5));
lean_inc_ref(v_xs_142_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1), 5, 4);
lean_closure_set(v___f_149_, 0, v_xs_142_);
lean_closure_set(v___f_149_, 1, v_inst_139_);
lean_closure_set(v___f_149_, 2, v_f_141_);
lean_closure_set(v___f_149_, 3, v_inst_140_);
v___x_150_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v_sz_151_ = lean_array_size(v_ys_143_);
v___x_152_ = ((size_t)0ULL);
v_positions_153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_150_, v___f_149_, v_sz_151_, v___x_152_, v_ys_143_);
v___x_154_ = lean_array_get_size(v_xs_142_);
lean_dec_ref(v_xs_142_);
v___x_155_ = l_Array_range(v___x_154_);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7));
v___x_187_ = lean_array_get_size(v_positions_153_);
v___x_188_ = lean_nat_dec_lt(v___x_185_, v___x_187_);
if (v___x_188_ == 0)
{
v___y_177_ = v___x_186_;
goto v___jp_176_;
}
else
{
lean_object* v___f_189_; uint8_t v___x_190_; 
v___f_189_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8));
v___x_190_ = lean_nat_dec_le(v___x_187_, v___x_187_);
if (v___x_190_ == 0)
{
if (v___x_188_ == 0)
{
v___y_177_ = v___x_186_;
goto v___jp_176_;
}
else
{
size_t v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_usize_of_nat(v___x_187_);
lean_inc(v_positions_153_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_150_, v___f_189_, v_positions_153_, v___x_152_, v___x_191_, v___x_186_);
v___y_177_ = v___x_192_;
goto v___jp_176_;
}
}
else
{
size_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_usize_of_nat(v___x_187_);
lean_inc(v_positions_153_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_150_, v___f_189_, v_positions_153_, v___x_152_, v___x_193_, v___x_186_);
v___y_177_ = v___x_194_;
goto v___jp_176_;
}
}
v___jp_144_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0);
v___x_146_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4);
v___x_147_ = l_panic___redArg(v___x_145_, v___x_146_);
return v___x_147_;
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = lean_array_get_size(v___x_155_);
v___x_159_ = lean_array_get_size(v___y_157_);
v___x_160_ = lean_nat_dec_eq(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v___y_157_);
lean_dec_ref(v___x_155_);
lean_dec(v_positions_153_);
goto v___jp_144_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = l_Array_isEqvAux___redArg(v___x_155_, v___y_157_, v___f_148_, v___x_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v___x_155_);
if (v___x_161_ == 0)
{
lean_dec(v_positions_153_);
goto v___jp_144_;
}
else
{
return v_positions_153_;
}
}
}
v___jp_162_:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_167_);
lean_dec(v___y_164_);
v___y_157_ = v___x_168_;
goto v___jp_156_;
}
v___jp_169_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_le(v___y_174_, v___y_173_);
if (v___x_175_ == 0)
{
lean_dec(v___y_173_);
lean_inc(v___y_174_);
v___y_163_ = v___y_170_;
v___y_164_ = v___y_171_;
v___y_165_ = v___y_172_;
v___y_166_ = v___y_174_;
v___y_167_ = v___y_174_;
goto v___jp_162_;
}
else
{
v___y_163_ = v___y_170_;
v___y_164_ = v___y_171_;
v___y_165_ = v___y_172_;
v___y_166_ = v___y_174_;
v___y_167_ = v___y_173_;
goto v___jp_162_;
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = lean_array_get_size(v___y_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_nat_dec_eq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6));
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_sub(v___x_178_, v___x_182_);
v___x_184_ = lean_nat_dec_le(v___x_179_, v___x_183_);
if (v___x_184_ == 0)
{
lean_inc(v___x_183_);
v___y_170_ = v___x_181_;
v___y_171_ = v___x_178_;
v___y_172_ = v___y_177_;
v___y_173_ = v___x_183_;
v___y_174_ = v___x_183_;
goto v___jp_169_;
}
else
{
v___y_170_ = v___x_181_;
v___y_171_ = v___x_178_;
v___y_172_ = v___y_177_;
v___y_173_ = v___x_183_;
v___y_174_ = v___x_179_;
goto v___jp_169_;
}
}
else
{
v___y_157_ = v___y_177_;
goto v___jp_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_f_199_, lean_object* v_xs_200_, lean_object* v_ys_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg(v_inst_197_, v_inst_198_, v_f_199_, v_xs_200_, v_ys_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(lean_object* v_inst_203_, lean_object* v_xs_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_array_get_borrowed(v_inst_203_, v_xs_204_, v_x_205_);
lean_inc(v___x_206_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(lean_object* v_inst_207_, lean_object* v_xs_208_, lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(v_inst_207_, v_xs_208_, v_x_209_);
lean_dec(v_x_209_);
lean_dec_ref(v_xs_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(lean_object* v___f_211_, lean_object* v_f_212_, lean_object* v_y_213_, lean_object* v_poss_214_){
_start:
{
lean_object* v___x_215_; size_t v_sz_216_; size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v_sz_216_ = lean_array_size(v_poss_214_);
v___x_217_ = ((size_t)0ULL);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_215_, v___f_211_, v_sz_216_, v___x_217_, v_poss_214_);
v___x_219_ = lean_apply_2(v_f_212_, v_y_213_, v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Array_instInhabited(lean_box(0));
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2));
v___x_224_ = lean_unsigned_to_nat(2u);
v___x_225_ = lean_unsigned_to_nat(73u);
v___x_226_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
v___x_227_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_228_ = l_mkPanicMessageWithDecl(v___x_227_, v___x_226_, v___x_225_, v___x_224_, v___x_223_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4));
v___x_231_ = lean_unsigned_to_nat(2u);
v___x_232_ = lean_unsigned_to_nat(74u);
v___x_233_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
v___x_234_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1));
v___x_235_ = l_mkPanicMessageWithDecl(v___x_234_, v___x_233_, v___x_232_, v___x_231_, v___x_230_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_f_240_, lean_object* v_positions_241_, lean_object* v_ys_242_, lean_object* v_xs_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_array_get_size(v_positions_241_);
v___x_245_ = lean_array_get_size(v_ys_242_);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_xs_243_);
lean_dec_ref(v_ys_242_);
lean_dec_ref(v_positions_241_);
lean_dec(v_f_240_);
lean_dec(v_inst_239_);
v___x_247_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
v___x_248_ = l_instInhabitedOfMonad___redArg(v_inst_238_, v___x_247_);
v___x_249_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3);
v___x_250_ = l_panic___redArg(v___x_248_, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_241_);
v___x_252_ = lean_array_get_size(v_xs_243_);
v___x_253_ = lean_nat_dec_eq(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_xs_243_);
lean_dec_ref(v_ys_242_);
lean_dec_ref(v_positions_241_);
lean_dec(v_f_240_);
lean_dec(v_inst_239_);
v___x_254_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0);
v___x_255_ = l_instInhabitedOfMonad___redArg(v_inst_238_, v___x_254_);
v___x_256_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5);
v___x_257_ = l_panic___redArg(v___x_255_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_258_, 0, v_inst_239_);
lean_closure_set(v___f_258_, 1, v_xs_243_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1), 4, 2);
lean_closure_set(v___f_259_, 0, v___f_258_);
lean_closure_set(v___f_259_, 1, v_f_240_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6));
v___x_262_ = l_Array_zipWithMAux___redArg(v_inst_238_, v_ys_242_, v_positions_241_, v___f_259_, v___x_260_, v___x_261_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object* v_00_u03b3_263_, lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_m_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_f_269_, lean_object* v_positions_270_, lean_object* v_ys_271_, lean_object* v_xs_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v_inst_267_, v_inst_268_, v_f_269_, v_positions_270_, v_ys_271_, v_xs_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_346_ = 0;
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_348_ = l_Lean_registerTraceClass(v___x_345_, v___x_346_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
return v_res_350_;
}
}
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
