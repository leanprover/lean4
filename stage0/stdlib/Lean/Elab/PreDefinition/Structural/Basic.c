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
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.PreDefinition.Structural.Basic"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Structural.Positions.groupAndSort"};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "assertion violation: Array.range xs.size == positions.flatten.qsort Nat.blt\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5;
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
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Structural.Positions.mapMwith"};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: positions.size = ys.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2;
static const lean_string_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: positions.numIndices = xs.size\n  "};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4;
static const lean_array_object l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_value;
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
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(lean_object* v_recArgPos_1_, lean_object* v_recFnName_2_, lean_object* v_e_3_){
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
LEAN_EXPORT void l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgPos_1_ = stack[0].m_obj;
lean_object* v_recFnName_2_ = stack[1].m_obj;
lean_object* v_e_3_ = stack[2].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(v_recArgPos_1_, v_recFnName_2_, v_e_3_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(lean_object* v_recArgPos_16_, lean_object* v_recFnName_17_, lean_object* v_e_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(v_recArgPos_16_, v_recFnName_17_, v_e_18_);
lean_dec_ref(v_e_18_);
lean_dec(v_recFnName_17_);
lean_dec(v_recArgPos_16_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object* v_recFnName_21_, lean_object* v_recArgPos_22_, lean_object* v_e_23_){
_start:
{
lean_object* v___f_24_; lean_object* v_app_x3f_25_; 
v___f_24_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed), 3, 2);
lean_closure_set(v___f_24_, 0, v_recArgPos_22_);
lean_closure_set(v___f_24_, 1, v_recFnName_21_);
v_app_x3f_25_ = lean_find_expr(v___f_24_, v_e_23_);
lean_dec_ref(v___f_24_);
if (lean_obj_tag(v_app_x3f_25_) == 0)
{
uint8_t v___x_26_; 
v___x_26_ = 0;
return v___x_26_;
}
else
{
uint8_t v___x_27_; 
lean_dec_ref_known(v_app_x3f_25_, 1);
v___x_27_ = 1;
return v___x_27_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_recArgHasLooseBVarsAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_recFnName_21_ = stack[0].m_obj;
lean_object* v_recArgPos_22_ = stack[1].m_obj;
lean_object* v_e_23_ = stack[2].m_obj;
uint8_t v_res_28_;
v_res_28_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_recFnName_21_, v_recArgPos_22_, v_e_23_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object* v_recFnName_29_, lean_object* v_recArgPos_30_, lean_object* v_e_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_recFnName_29_, v_recArgPos_30_, v_e_31_);
lean_dec_ref(v_e_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(lean_object* v_as_34_, size_t v_i_35_, size_t v_stop_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_eq(v_i_35_, v_stop_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; size_t v___x_42_; size_t v___x_43_; 
v___x_39_ = lean_array_uget_borrowed(v_as_34_, v_i_35_);
v___x_40_ = lean_array_get_size(v___x_39_);
v___x_41_ = lean_nat_add(v_b_37_, v___x_40_);
lean_dec(v_b_37_);
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_add(v_i_35_, v___x_42_);
v_i_35_ = v___x_43_;
v_b_37_ = v___x_41_;
goto _start;
}
else
{
return v_b_37_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_34_ = stack[0].m_obj;
size_t v_i_35_ = stack[1].m_num;
size_t v_stop_36_ = stack[2].m_num;
lean_object* v_b_37_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_as_34_, v_i_35_, v_stop_36_, v_b_37_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(lean_object* v_as_46_, lean_object* v_i_47_, lean_object* v_stop_48_, lean_object* v_b_49_){
_start:
{
size_t v_i_boxed_50_; size_t v_stop_boxed_51_; lean_object* v_res_52_; 
v_i_boxed_50_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_stop_boxed_51_ = lean_unbox_usize(v_stop_48_);
lean_dec(v_stop_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_as_46_, v_i_boxed_50_, v_stop_boxed_51_, v_b_49_);
lean_dec_ref(v_as_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices(lean_object* v_positions_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_array_get_size(v_positions_53_);
v___x_56_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
if (v___x_56_ == 0)
{
return v___x_54_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_le(v___x_55_, v___x_55_);
if (v___x_57_ == 0)
{
if (v___x_56_ == 0)
{
return v___x_54_;
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_55_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_53_, v___x_58_, v___x_59_, v___x_54_);
return v___x_60_;
}
}
else
{
size_t v___x_61_; size_t v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((size_t)0ULL);
v___x_62_ = lean_usize_of_nat(v___x_55_);
v___x_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_53_, v___x_61_, v___x_62_, v___x_54_);
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_numIndices___boxed(lean_object* v_positions_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_64_);
lean_dec_ref(v_positions_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(lean_object* v_inst_66_, lean_object* v_xs_67_, lean_object* v_f_68_, lean_object* v_inst_69_, lean_object* v_x_70_, lean_object* v_x1_71_, lean_object* v_x2_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_73_ = lean_array_get_borrowed(v_inst_66_, v_xs_67_, v_x2_72_);
lean_inc(v___x_73_);
v___x_74_ = lean_apply_1(v_f_68_, v___x_73_);
v___x_75_ = lean_apply_2(v_inst_69_, v___x_74_, v_x_70_);
v___x_76_ = lean_unbox(v___x_75_);
if (v___x_76_ == 0)
{
lean_dec(v_x2_72_);
return v_x1_71_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_array_push(v_x1_71_, v_x2_72_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(lean_object* v_inst_78_, lean_object* v_xs_79_, lean_object* v_f_80_, lean_object* v_inst_81_, lean_object* v_x_82_, lean_object* v_x1_83_, lean_object* v_x2_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(v_inst_78_, v_xs_79_, v_f_80_, v_inst_81_, v_x_82_, v_x1_83_, v_x2_84_);
lean_dec_ref(v_xs_79_);
lean_dec(v_inst_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(lean_object* v_xs_107_, lean_object* v_inst_108_, lean_object* v_f_109_, lean_object* v_inst_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_112_ = lean_array_get_size(v_xs_107_);
v___x_113_ = l_Array_range(v___x_112_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_get_size(v___x_113_);
v___x_116_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0));
v___x_117_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v___x_118_ = lean_nat_dec_lt(v___x_114_, v___x_115_);
if (v___x_118_ == 0)
{
lean_dec_ref(v___x_113_);
lean_dec(v_x_111_);
lean_dec_ref(v_inst_110_);
lean_dec(v_f_109_);
lean_dec(v_inst_108_);
lean_dec_ref(v_xs_107_);
return v___x_116_;
}
else
{
lean_object* v___f_119_; uint8_t v___x_120_; 
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_119_, 0, v_inst_108_);
lean_closure_set(v___f_119_, 1, v_xs_107_);
lean_closure_set(v___f_119_, 2, v_f_109_);
lean_closure_set(v___f_119_, 3, v_inst_110_);
lean_closure_set(v___f_119_, 4, v_x_111_);
v___x_120_ = lean_nat_dec_le(v___x_115_, v___x_115_);
if (v___x_120_ == 0)
{
if (v___x_118_ == 0)
{
lean_dec_ref(v___f_119_);
lean_dec_ref(v___x_113_);
return v___x_116_;
}
else
{
size_t v___x_121_; size_t v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((size_t)0ULL);
v___x_122_ = lean_usize_of_nat(v___x_115_);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_117_, v___f_119_, v___x_113_, v___x_121_, v___x_122_, v___x_116_);
return v___x_123_;
}
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_115_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_117_, v___f_119_, v___x_113_, v___x_124_, v___x_125_, v___x_116_);
return v___x_126_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Array_instInhabited___redArg();
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_132_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4));
v___x_133_ = lean_unsigned_to_nat(2u);
v___x_134_ = lean_unsigned_to_nat(63u);
v___x_135_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3));
v___x_136_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
v___x_137_ = l_mkPanicMessageWithDecl(v___x_136_, v___x_135_, v___x_134_, v___x_133_, v___x_132_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___redArg(lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_xs_145_, lean_object* v_ys_146_){
_start:
{
lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_153_; size_t v_sz_154_; size_t v___x_155_; lean_object* v_positions_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___y_160_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_180_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___f_147_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0));
lean_inc_ref(v_xs_145_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1), 5, 4);
lean_closure_set(v___f_148_, 0, v_xs_145_);
lean_closure_set(v___f_148_, 1, v_inst_142_);
lean_closure_set(v___f_148_, 2, v_f_144_);
lean_closure_set(v___f_148_, 3, v_inst_143_);
v___x_149_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1);
v___x_153_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10));
v_sz_154_ = lean_array_size(v_ys_146_);
v___x_155_ = ((size_t)0ULL);
v_positions_156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_153_, v___f_148_, v_sz_154_, v___x_155_, v_ys_146_);
v___x_157_ = lean_array_get_size(v_xs_145_);
lean_dec_ref(v_xs_145_);
v___x_158_ = l_Array_range(v___x_157_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7));
v___x_190_ = lean_array_get_size(v_positions_156_);
v___x_191_ = lean_nat_dec_lt(v___x_188_, v___x_190_);
if (v___x_191_ == 0)
{
v___y_180_ = v___x_189_;
goto v___jp_179_;
}
else
{
lean_object* v___f_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___f_192_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8));
v___x_193_ = lean_usize_of_nat(v___x_190_);
lean_inc(v_positions_156_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_153_, v___f_192_, v_positions_156_, v___x_155_, v___x_193_, v___x_189_);
v___y_180_ = v___x_194_;
goto v___jp_179_;
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5);
v___x_152_ = l_panic___redArg(v___x_149_, v___x_151_);
return v___x_152_;
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_array_get_size(v___x_158_);
v___x_162_ = lean_array_get_size(v___y_160_);
v___x_163_ = lean_nat_dec_eq(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec_ref(v___y_160_);
lean_dec_ref(v___x_158_);
lean_dec(v_positions_156_);
goto v___jp_150_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = l_Array_isEqvAux___redArg(v___x_158_, v___y_160_, v___f_147_, v___x_161_);
lean_dec_ref(v___y_160_);
lean_dec_ref(v___x_158_);
if (v___x_164_ == 0)
{
lean_dec(v_positions_156_);
goto v___jp_150_;
}
else
{
return v_positions_156_;
}
}
}
v___jp_165_:
{
lean_object* v___x_171_; 
lean_inc_ref(v___y_168_);
v___x_171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_168_, v___y_169_, v___y_167_, v___y_166_, v___y_170_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_170_);
lean_dec(v___y_169_);
v___y_160_ = v___x_171_;
goto v___jp_159_;
}
v___jp_172_:
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_le(v___y_177_, v___y_174_);
if (v___x_178_ == 0)
{
lean_dec(v___y_174_);
lean_inc(v___y_177_);
v___y_166_ = v___y_177_;
v___y_167_ = v___y_173_;
v___y_168_ = v___y_175_;
v___y_169_ = v___y_176_;
v___y_170_ = v___y_177_;
goto v___jp_165_;
}
else
{
v___y_166_ = v___y_177_;
v___y_167_ = v___y_173_;
v___y_168_ = v___y_175_;
v___y_169_ = v___y_176_;
v___y_170_ = v___y_174_;
goto v___jp_165_;
}
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_array_get_size(v___y_180_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_nat_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6));
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_sub(v___x_181_, v___x_185_);
v___x_187_ = lean_nat_dec_le(v___x_182_, v___x_186_);
if (v___x_187_ == 0)
{
lean_inc(v___x_186_);
v___y_173_ = v___y_180_;
v___y_174_ = v___x_186_;
v___y_175_ = v___x_184_;
v___y_176_ = v___x_181_;
v___y_177_ = v___x_186_;
goto v___jp_172_;
}
else
{
v___y_173_ = v___y_180_;
v___y_174_ = v___x_186_;
v___y_175_ = v___x_184_;
v___y_176_ = v___x_181_;
v___y_177_ = v___x_182_;
goto v___jp_172_;
}
}
else
{
v___y_160_ = v___y_180_;
goto v___jp_159_;
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
lean_dec(v_inst_207_);
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
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_222_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1));
v___x_223_ = lean_unsigned_to_nat(2u);
v___x_224_ = lean_unsigned_to_nat(73u);
v___x_225_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0));
v___x_226_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
v___x_227_ = l_mkPanicMessageWithDecl(v___x_226_, v___x_225_, v___x_224_, v___x_223_, v___x_222_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_229_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3));
v___x_230_ = lean_unsigned_to_nat(2u);
v___x_231_ = lean_unsigned_to_nat(74u);
v___x_232_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0));
v___x_233_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2));
v___x_234_ = l_mkPanicMessageWithDecl(v___x_233_, v___x_232_, v___x_231_, v___x_230_, v___x_229_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___redArg(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_f_239_, lean_object* v_positions_240_, lean_object* v_ys_241_, lean_object* v_xs_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_array_get_size(v_positions_240_);
v___x_244_ = lean_array_get_size(v_ys_241_);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1, &l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_once, _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1);
lean_inc_ref(v_inst_237_);
v___x_247_ = l_instInhabitedOfMonad___redArg(v_inst_237_, v___x_246_);
if (v___x_245_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v_xs_242_);
lean_dec_ref(v_ys_241_);
lean_dec_ref(v_positions_240_);
lean_dec(v_f_239_);
lean_dec(v_inst_238_);
lean_dec_ref(v_inst_237_);
v___x_248_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2);
v___x_249_ = l_panic___redArg(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_240_);
v___x_251_ = lean_array_get_size(v_xs_242_);
v___x_252_ = lean_nat_dec_eq(v___x_250_, v___x_251_);
lean_dec(v___x_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v_xs_242_);
lean_dec_ref(v_ys_241_);
lean_dec_ref(v_positions_240_);
lean_dec(v_f_239_);
lean_dec(v_inst_238_);
lean_dec_ref(v_inst_237_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4, &l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4);
v___x_254_ = l_panic___redArg(v___x_247_, v___x_253_);
lean_dec(v___x_247_);
return v___x_254_;
}
else
{
lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v___x_247_);
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_255_, 0, v_inst_238_);
lean_closure_set(v___f_255_, 1, v_xs_242_);
v___f_256_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1), 4, 2);
lean_closure_set(v___f_256_, 0, v___f_255_);
lean_closure_set(v___f_256_, 1, v_f_239_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5));
v___x_259_ = l_Array_zipWithMAux___redArg(v_inst_237_, v_ys_241_, v_positions_240_, v___f_256_, v___x_257_, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith(lean_object* v_00_u03b3_260_, lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_m_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_f_266_, lean_object* v_positions_267_, lean_object* v_ys_268_, lean_object* v_xs_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v_inst_264_, v_inst_265_, v_f_266_, v_positions_267_, v_ys_268_, v_xs_269_);
return v___x_270_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_343_ = 0;
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_));
v___x_345_ = l_Lean_registerTraceClass(v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_346_;
v_res_346_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
return v_res_348_;
}
}
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
