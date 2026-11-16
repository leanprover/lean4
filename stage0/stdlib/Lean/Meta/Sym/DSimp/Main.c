// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Main
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.DSimproc import Lean.Meta.Sym.DSimp.App import Lean.Meta.Sym.DSimp.Lambda import Lean.Meta.Sym.DSimp.Forall import Lean.Meta.Sym.DSimp.Let import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateMVarsS
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
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "unexpected kernel projection term during simplification"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "\npre-process and fold them as projection applications"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`dsimp` failed: maximum number of steps exceeded"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2;
LEAN_EXPORT lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(lean_object* v_d_1_, lean_object* v_e_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*13);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_dec_ref_known(v___x_16_, 1);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
lean_dec_ref(v_e_2_);
lean_dec(v_d_1_);
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_mdata___override(v_d_1_, v_e_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(lean_object* v_d_25_, lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_25_, v_e_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(lean_object* v_d_35_, lean_object* v_e_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_35_, v_e_36_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(lean_object* v_d_48_, lean_object* v_e_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_48_, v_e_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_env_68_; uint8_t v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v_toCold_72_; lean_object* v_mctx_73_; lean_object* v_lctx_74_; lean_object* v_options_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = 0;
v_env_70_ = l_Lean_Environment_setRecordingDeps(v_env_68_, v___x_69_);
v___x_71_ = lean_st_ref_get(v___y_63_);
v_toCold_72_ = lean_ctor_get(v___y_64_, 0);
v_mctx_73_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_mctx_73_);
lean_dec(v___x_71_);
v_lctx_74_ = lean_ctor_get(v___y_62_, 2);
v_options_75_ = lean_ctor_get(v_toCold_72_, 2);
lean_inc_ref(v_options_75_);
lean_inc_ref(v_lctx_74_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_70_);
lean_ctor_set(v___x_76_, 1, v_mctx_73_);
lean_ctor_set(v___x_76_, 2, v_lctx_74_);
lean_ctor_set(v___x_76_, 3, v_options_75_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_61_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object* v_msg_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_ref_92_; lean_object* v___x_93_; lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v_ref_92_ = lean_ctor_get(v___y_89_, 2);
v___x_93_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
lean_inc(v_ref_92_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_ref_92_);
lean_ctor_set(v___x_98_, 1, v_a_94_);
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 1);
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object* v_msg_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3));
v___x_117_ = l_Lean_stringToMessageData(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object* v_e_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_a_130_; 
switch(lean_obj_tag(v_e_118_))
{
case 2:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Sym_instantiateAssignedMVarHeadS_x3f(v_e_118_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_149_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_149_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_149_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_149_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
if (lean_obj_tag(v_a_135_) == 1)
{
lean_object* v_val_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v_val_139_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_a_135_, 1);
v___x_140_ = 0;
v___x_141_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_141_, 0, v_val_139_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_140_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_141_);
v___x_143_ = v___x_137_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_147_; 
lean_dec(v_a_135_);
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_145_);
v___x_147_ = v___x_137_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_134_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_134_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
case 5:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_158_;
}
case 6:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_159_;
}
case 7:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_160_;
}
case 8:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_161_;
}
case 10:
{
lean_object* v_data_162_; lean_object* v_expr_163_; lean_object* v___x_164_; 
v_data_162_ = lean_ctor_get(v_e_118_, 0);
v_expr_163_ = lean_ctor_get(v_e_118_, 1);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
lean_inc(v_a_119_);
lean_inc_ref(v_expr_163_);
v___x_164_ = lean_sym_dsimp(v_expr_163_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_187_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_187_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_187_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_187_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (lean_obj_tag(v_a_165_) == 0)
{
lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec_ref_known(v_a_165_, 0);
lean_dec_ref_known(v_e_118_, 2);
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v_e_x27_173_; size_t v___x_174_; size_t v___x_175_; uint8_t v___x_176_; 
lean_del_object(v___x_167_);
v_e_x27_173_ = lean_ctor_get(v_a_165_, 0);
lean_inc_ref(v_e_x27_173_);
lean_dec_ref_known(v_a_165_, 1);
v___x_174_ = lean_ptr_addr(v_expr_163_);
v___x_175_ = lean_ptr_addr(v_e_x27_173_);
v___x_176_ = lean_usize_dec_eq(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_inc(v_data_162_);
lean_dec_ref_known(v_e_118_, 2);
v___x_177_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_162_, v_e_x27_173_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_a_130_ = v_a_178_;
goto v___jp_129_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_173_);
v_a_130_ = v_e_118_;
goto v___jp_129_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_118_, 2);
return v___x_164_;
}
}
case 11:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_188_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
v___x_189_ = l_Lean_indentExpr(v_e_118_);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_192_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
return v___x_193_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_e_118_);
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
v___jp_129_:
{
uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_132_, 0, v_a_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object* v_00_u03b1_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_209_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object* v_00_u03b1_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_221_, v_msg_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object* v_e_236_, lean_object* v_r_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___f_240_; lean_object* v___f_241_; uint8_t v___x_242_; 
v___f_240_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_241_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
v___x_242_ = l_Lean_Expr_hasMVar(v_e_236_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v_numSteps_244_; lean_object* v_cache_245_; lean_object* v_transientCache_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
v___x_243_ = lean_st_ref_take(v_a_238_);
v_numSteps_244_ = lean_ctor_get(v___x_243_, 0);
v_cache_245_ = lean_ctor_get(v___x_243_, 1);
v_transientCache_246_ = lean_ctor_get(v___x_243_, 2);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_256_ == 0)
{
v___x_248_ = v___x_243_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_transientCache_246_);
lean_inc(v_cache_245_);
lean_inc(v_numSteps_244_);
lean_dec(v___x_243_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc_ref(v_r_237_);
v___x_250_ = l_Lean_PersistentHashMap_insert___redArg(v___f_240_, v___f_241_, v_cache_245_, v_e_236_, v_r_237_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_numSteps_244_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_transientCache_246_);
v___x_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_st_ref_put(v_a_238_, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_r_237_);
return v___x_254_;
}
}
}
else
{
lean_object* v___x_257_; lean_object* v_numSteps_258_; lean_object* v_cache_259_; lean_object* v_transientCache_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_270_; 
v___x_257_ = lean_st_ref_take(v_a_238_);
v_numSteps_258_ = lean_ctor_get(v___x_257_, 0);
v_cache_259_ = lean_ctor_get(v___x_257_, 1);
v_transientCache_260_ = lean_ctor_get(v___x_257_, 2);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_270_ == 0)
{
v___x_262_ = v___x_257_;
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_transientCache_260_);
lean_inc(v_cache_259_);
lean_inc(v_numSteps_258_);
lean_dec(v___x_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_inc_ref(v_r_237_);
v___x_264_ = l_Lean_PersistentHashMap_insert___redArg(v___f_240_, v___f_241_, v_transientCache_260_, v_e_236_, v_r_237_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 2, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_numSteps_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_cache_259_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_264_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_st_ref_put(v_a_238_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_r_237_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object* v_e_271_, lean_object* v_r_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(v_e_271_, v_r_272_, v_a_273_);
lean_dec(v_a_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object* v_e_276_, lean_object* v_r_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___f_288_; lean_object* v___f_289_; uint8_t v___x_290_; 
v___f_288_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_289_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
v___x_290_ = l_Lean_Expr_hasMVar(v_e_276_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v_numSteps_292_; lean_object* v_cache_293_; lean_object* v_transientCache_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v___x_291_ = lean_st_ref_take(v_a_280_);
v_numSteps_292_ = lean_ctor_get(v___x_291_, 0);
v_cache_293_ = lean_ctor_get(v___x_291_, 1);
v_transientCache_294_ = lean_ctor_get(v___x_291_, 2);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v___x_291_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_transientCache_294_);
lean_inc(v_cache_293_);
lean_inc(v_numSteps_292_);
lean_dec(v___x_291_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_inc_ref(v_r_277_);
v___x_298_ = l_Lean_PersistentHashMap_insert___redArg(v___f_288_, v___f_289_, v_cache_293_, v_e_276_, v_r_277_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_numSteps_292_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_transientCache_294_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_st_ref_put(v_a_280_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_r_277_);
return v___x_302_;
}
}
}
else
{
lean_object* v___x_305_; lean_object* v_numSteps_306_; lean_object* v_cache_307_; lean_object* v_transientCache_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v___x_305_ = lean_st_ref_take(v_a_280_);
v_numSteps_306_ = lean_ctor_get(v___x_305_, 0);
v_cache_307_ = lean_ctor_get(v___x_305_, 1);
v_transientCache_308_ = lean_ctor_get(v___x_305_, 2);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_318_ == 0)
{
v___x_310_ = v___x_305_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_transientCache_308_);
lean_inc(v_cache_307_);
lean_inc(v_numSteps_306_);
lean_dec(v___x_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_inc_ref(v_r_277_);
v___x_312_ = l_Lean_PersistentHashMap_insert___redArg(v___f_288_, v___f_289_, v_transientCache_308_, v_e_276_, v_r_277_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_numSteps_306_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_cache_307_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v___x_312_);
v___x_314_ = v_reuseFailAlloc_317_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_st_ref_put(v_a_280_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_r_277_);
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object* v_e_319_, lean_object* v_r_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(v_e_319_, v_r_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
return v_res_331_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_maxRecDepthErrorMessage;
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
v___x_340_ = l_Lean_MessageData_ofFormat(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
v___x_342_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2));
v___x_343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object* v_ref_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_ref_344_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object* v_ref_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object* v_00_u03b1_352_, lean_object* v_ref_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_353_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object* v_00_u03b1_365_, lean_object* v_ref_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_365_, v_ref_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_post_390_; lean_object* v___x_391_; 
v_post_390_ = lean_ctor_get(v___y_380_, 1);
lean_inc_ref(v_post_390_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
lean_inc(v___y_380_);
v___x_391_ = lean_apply_11(v_post_390_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, lean_box(0));
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_ks_409_; lean_object* v_vs_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_436_; 
v_ks_409_ = lean_ctor_get(v_x_405_, 0);
v_vs_410_ = lean_ctor_get(v_x_405_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_436_ == 0)
{
v___x_412_ = v_x_405_;
v_isShared_413_ = v_isSharedCheck_436_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_vs_410_);
lean_inc(v_ks_409_);
lean_dec(v_x_405_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_436_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_ks_409_);
v___x_415_ = lean_nat_dec_lt(v_x_406_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_x_406_);
v___x_416_ = lean_array_push(v_ks_409_, v_x_407_);
v___x_417_ = lean_array_push(v_vs_410_, v_x_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_417_);
lean_ctor_set(v___x_412_, 0, v___x_416_);
v___x_419_ = v___x_412_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
lean_object* v_k_x27_421_; size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v_k_x27_421_ = lean_array_fget_borrowed(v_ks_409_, v_x_406_);
v___x_422_ = lean_ptr_addr(v_x_407_);
v___x_423_ = lean_ptr_addr(v_k_x27_421_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_426_; 
if (v_isShared_413_ == 0)
{
v___x_426_ = v___x_412_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_ks_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_vs_410_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_x_406_, v___x_427_);
lean_dec(v_x_406_);
v_x_405_ = v___x_426_;
v_x_406_ = v___x_428_;
goto _start;
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = lean_array_fset(v_ks_409_, v_x_406_, v_x_407_);
v___x_432_ = lean_array_fset(v_vs_410_, v_x_406_, v_x_408_);
lean_dec(v_x_406_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_432_);
lean_ctor_set(v___x_412_, 0, v___x_431_);
v___x_434_ = v___x_412_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_437_, lean_object* v_k_438_, lean_object* v_v_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_437_, v___x_440_, v_k_438_, v_v_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object* v_x_443_, size_t v_x_444_, size_t v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_object* v_es_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v_j_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_es_448_ = lean_ctor_get(v_x_443_, 0);
v___x_449_ = ((size_t)31ULL);
v___x_450_ = lean_usize_land(v_x_444_, v___x_449_);
v_j_451_ = lean_usize_to_nat(v___x_450_);
v___x_452_ = lean_array_get_size(v_es_448_);
v___x_453_ = lean_nat_dec_lt(v_j_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v_j_451_);
lean_dec(v_x_447_);
lean_dec_ref(v_x_446_);
return v_x_443_;
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_494_; 
lean_inc_ref(v_es_448_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_x_443_, 0);
lean_dec(v_unused_495_);
v___x_455_ = v_x_443_;
v_isShared_456_ = v_isSharedCheck_494_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_x_443_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_494_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_v_457_; lean_object* v___x_458_; lean_object* v_xs_x27_459_; lean_object* v___y_461_; 
v_v_457_ = lean_array_fget(v_es_448_, v_j_451_);
v___x_458_ = lean_box(0);
v_xs_x27_459_ = lean_array_fset(v_es_448_, v_j_451_, v___x_458_);
switch(lean_obj_tag(v_v_457_))
{
case 0:
{
lean_object* v_key_466_; lean_object* v_val_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_479_; 
v_key_466_ = lean_ctor_get(v_v_457_, 0);
v_val_467_ = lean_ctor_get(v_v_457_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_v_457_);
if (v_isSharedCheck_479_ == 0)
{
v___x_469_ = v_v_457_;
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_val_467_);
lean_inc(v_key_466_);
lean_dec(v_v_457_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
size_t v___x_471_; size_t v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_ptr_addr(v_x_446_);
v___x_472_ = lean_ptr_addr(v_key_466_);
v___x_473_ = lean_usize_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_del_object(v___x_469_);
v___x_474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_466_, v_val_467_, v_x_446_, v_x_447_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___y_461_ = v___x_475_;
goto v___jp_460_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v_val_467_);
lean_dec(v_key_466_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v_x_447_);
lean_ctor_set(v___x_469_, 0, v_x_446_);
v___x_477_ = v___x_469_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_x_446_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_x_447_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v___y_461_ = v___x_477_;
goto v___jp_460_;
}
}
}
}
case 1:
{
lean_object* v_node_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
v_node_480_ = lean_ctor_get(v_v_457_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_v_457_);
if (v_isSharedCheck_492_ == 0)
{
v___x_482_ = v_v_457_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_node_480_);
lean_dec(v_v_457_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_484_ = ((size_t)5ULL);
v___x_485_ = lean_usize_shift_right(v_x_444_, v___x_484_);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_x_445_, v___x_486_);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_node_480_, v___x_485_, v___x_487_, v_x_446_, v_x_447_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
v___y_461_ = v___x_490_;
goto v___jp_460_;
}
}
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_x_446_);
lean_ctor_set(v___x_493_, 1, v_x_447_);
v___y_461_ = v___x_493_;
goto v___jp_460_;
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_array_fset(v_xs_x27_459_, v_j_451_, v___y_461_);
lean_dec(v_j_451_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_462_);
v___x_464_ = v___x_455_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_object* v_ks_496_; lean_object* v_vs_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_515_; 
v_ks_496_ = lean_ctor_get(v_x_443_, 0);
v_vs_497_ = lean_ctor_get(v_x_443_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_515_ == 0)
{
v___x_499_ = v_x_443_;
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_vs_497_);
lean_inc(v_ks_496_);
lean_dec(v_x_443_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_ks_496_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_vs_497_);
v___x_502_ = v_reuseFailAlloc_514_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v_newNode_503_; size_t v___x_504_; uint8_t v___x_505_; 
v_newNode_503_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v___x_502_, v_x_446_, v_x_447_);
v___x_504_ = ((size_t)7ULL);
v___x_505_ = lean_usize_dec_le(v___x_504_, v_x_445_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_503_);
v___x_507_ = lean_unsigned_to_nat(4u);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
if (v___x_508_ == 0)
{
lean_object* v_ks_509_; lean_object* v_vs_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_ks_509_ = lean_ctor_get(v_newNode_503_, 0);
lean_inc_ref(v_ks_509_);
v_vs_510_ = lean_ctor_get(v_newNode_503_, 1);
lean_inc_ref(v_vs_510_);
lean_dec_ref(v_newNode_503_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
v___x_513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_445_, v_ks_509_, v_vs_510_, v___x_511_, v___x_512_);
lean_dec_ref(v_vs_510_);
lean_dec_ref(v_ks_509_);
return v___x_513_;
}
else
{
return v_newNode_503_;
}
}
else
{
return v_newNode_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_516_, lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_i_519_, lean_object* v_entries_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_keys_517_);
v___x_522_ = lean_nat_dec_lt(v_i_519_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v_i_519_);
return v_entries_520_;
}
else
{
lean_object* v_k_523_; lean_object* v_v_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; uint64_t v___x_528_; size_t v_h_529_; size_t v___x_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v_h_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_k_523_ = lean_array_fget_borrowed(v_keys_517_, v_i_519_);
v_v_524_ = lean_array_fget_borrowed(v_vals_518_, v_i_519_);
v___x_525_ = lean_ptr_addr(v_k_523_);
v___x_526_ = ((size_t)3ULL);
v___x_527_ = lean_usize_shift_right(v___x_525_, v___x_526_);
v___x_528_ = lean_usize_to_uint64(v___x_527_);
v_h_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = ((size_t)5ULL);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_sub(v_depth_516_, v___x_532_);
v___x_534_ = lean_usize_mul(v___x_530_, v___x_533_);
v_h_535_ = lean_usize_shift_right(v_h_529_, v___x_534_);
v___x_536_ = lean_nat_add(v_i_519_, v___x_531_);
lean_dec(v_i_519_);
lean_inc(v_v_524_);
lean_inc(v_k_523_);
v___x_537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_entries_520_, v_h_535_, v_depth_516_, v_k_523_, v_v_524_);
v_i_519_ = v___x_536_;
v_entries_520_ = v___x_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_539_, lean_object* v_keys_540_, lean_object* v_vals_541_, lean_object* v_i_542_, lean_object* v_entries_543_){
_start:
{
size_t v_depth_boxed_544_; lean_object* v_res_545_; 
v_depth_boxed_544_ = lean_unbox_usize(v_depth_539_);
lean_dec(v_depth_539_);
v_res_545_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_544_, v_keys_540_, v_vals_541_, v_i_542_, v_entries_543_);
lean_dec_ref(v_vals_541_);
lean_dec_ref(v_keys_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
size_t v_x_44959__boxed_551_; size_t v_x_44960__boxed_552_; lean_object* v_res_553_; 
v_x_44959__boxed_551_ = lean_unbox_usize(v_x_547_);
lean_dec(v_x_547_);
v_x_44960__boxed_552_ = lean_unbox_usize(v_x_548_);
lean_dec(v_x_548_);
v_res_553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_546_, v_x_44959__boxed_551_, v_x_44960__boxed_552_, v_x_549_, v_x_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; uint64_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_557_ = lean_ptr_addr(v_x_555_);
v___x_558_ = ((size_t)3ULL);
v___x_559_ = lean_usize_shift_right(v___x_557_, v___x_558_);
v___x_560_ = lean_usize_to_uint64(v___x_559_);
v___x_561_ = lean_uint64_to_usize(v___x_560_);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_554_, v___x_561_, v___x_562_, v_x_555_, v_x_556_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_k_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_keys_564_);
v___x_569_ = lean_nat_dec_lt(v_i_566_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v_i_566_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
lean_object* v_k_x27_571_; size_t v___x_572_; size_t v___x_573_; uint8_t v___x_574_; 
v_k_x27_571_ = lean_array_fget_borrowed(v_keys_564_, v_i_566_);
v___x_572_ = lean_ptr_addr(v_k_567_);
v___x_573_ = lean_ptr_addr(v_k_x27_571_);
v___x_574_ = lean_usize_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_i_566_, v___x_575_);
lean_dec(v_i_566_);
v_i_566_ = v___x_576_;
goto _start;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_array_fget_borrowed(v_vals_565_, v_i_566_);
lean_dec(v_i_566_);
lean_inc(v___x_578_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_580_, lean_object* v_vals_581_, lean_object* v_i_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_580_, v_vals_581_, v_i_582_, v_k_583_);
lean_dec_ref(v_k_583_);
lean_dec_ref(v_vals_581_);
lean_dec_ref(v_keys_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object* v_x_585_, size_t v_x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v_es_588_; lean_object* v___x_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v_j_592_; lean_object* v___x_593_; 
v_es_588_ = lean_ctor_get(v_x_585_, 0);
v___x_589_ = lean_box(2);
v___x_590_ = ((size_t)31ULL);
v___x_591_ = lean_usize_land(v_x_586_, v___x_590_);
v_j_592_ = lean_usize_to_nat(v___x_591_);
v___x_593_ = lean_array_get_borrowed(v___x_589_, v_es_588_, v_j_592_);
lean_dec(v_j_592_);
switch(lean_obj_tag(v___x_593_))
{
case 0:
{
lean_object* v_key_594_; lean_object* v_val_595_; size_t v___x_596_; size_t v___x_597_; uint8_t v___x_598_; 
v_key_594_ = lean_ctor_get(v___x_593_, 0);
v_val_595_ = lean_ctor_get(v___x_593_, 1);
v___x_596_ = lean_ptr_addr(v_x_587_);
v___x_597_ = lean_ptr_addr(v_key_594_);
v___x_598_ = lean_usize_dec_eq(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_600_; 
lean_inc(v_val_595_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_val_595_);
return v___x_600_;
}
}
case 1:
{
lean_object* v_node_601_; size_t v___x_602_; size_t v___x_603_; 
v_node_601_ = lean_ctor_get(v___x_593_, 0);
v___x_602_ = ((size_t)5ULL);
v___x_603_ = lean_usize_shift_right(v_x_586_, v___x_602_);
v_x_585_ = v_node_601_;
v_x_586_ = v___x_603_;
goto _start;
}
default: 
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(0);
return v___x_605_;
}
}
}
else
{
lean_object* v_ks_606_; lean_object* v_vs_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_ks_606_ = lean_ctor_get(v_x_585_, 0);
v_vs_607_ = lean_ctor_get(v_x_585_, 1);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_606_, v_vs_607_, v___x_608_, v_x_587_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_45160__boxed_613_; lean_object* v_res_614_; 
v_x_45160__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_614_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_610_, v_x_45160__boxed_613_, v_x_612_);
lean_dec_ref(v_x_612_);
lean_dec_ref(v_x_610_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; uint64_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_617_ = lean_ptr_addr(v_x_616_);
v___x_618_ = ((size_t)3ULL);
v___x_619_ = lean_usize_shift_right(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_to_uint64(v___x_619_);
v___x_621_ = lean_uint64_to_usize(v___x_620_);
v___x_622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_615_, v___x_621_, v_x_616_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_623_, v_x_624_);
lean_dec_ref(v_x_624_);
lean_dec_ref(v_x_623_);
return v_res_625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* lean_sym_dsimp(lean_object* v_e_u2081_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_r_642_; lean_object* v___y_643_; lean_object* v_e_u2082_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v_a_698_; lean_object* v_e_x27_699_; uint8_t v_done_700_; lean_object* v_toCold_701_; lean_object* v_currRecDepth_702_; lean_object* v_ref_703_; uint16_t v_optionFlags_704_; uint8_t v_suppressElabErrors_705_; uint8_t v_checkDeprecated_706_; uint8_t v_isRecordingDeps_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_840_; 
v_toCold_701_ = lean_ctor_get(v_a_638_, 0);
v_currRecDepth_702_ = lean_ctor_get(v_a_638_, 1);
v_ref_703_ = lean_ctor_get(v_a_638_, 2);
v_optionFlags_704_ = lean_ctor_get_uint16(v_a_638_, sizeof(void*)*3);
v_suppressElabErrors_705_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*3 + 2);
v_checkDeprecated_706_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*3 + 3);
v_isRecordingDeps_707_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*3 + 4);
v_isSharedCheck_840_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_840_ == 0)
{
v___x_709_ = v_a_638_;
v_isShared_710_ = v_isSharedCheck_840_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_ref_703_);
lean_inc(v_currRecDepth_702_);
lean_inc(v_toCold_701_);
lean_dec(v_a_638_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_840_;
goto v_resetjp_708_;
}
v___jp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_Expr_hasMVar(v_e_u2081_630_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v_numSteps_646_; lean_object* v_cache_647_; lean_object* v_transientCache_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_658_; 
v___x_645_ = lean_st_ref_take(v___y_643_);
v_numSteps_646_ = lean_ctor_get(v___x_645_, 0);
v_cache_647_ = lean_ctor_get(v___x_645_, 1);
v_transientCache_648_ = lean_ctor_get(v___x_645_, 2);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_650_ = v___x_645_;
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_transientCache_648_);
lean_inc(v_cache_647_);
lean_inc(v_numSteps_646_);
lean_dec(v___x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
lean_inc_ref(v_r_642_);
v___x_652_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_647_, v_e_u2081_630_, v_r_642_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_numSteps_646_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_transientCache_648_);
v___x_654_ = v_reuseFailAlloc_657_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_st_ref_put(v___y_643_, v___x_654_);
lean_dec(v___y_643_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_r_642_);
return v___x_656_;
}
}
}
else
{
lean_object* v___x_659_; lean_object* v_numSteps_660_; lean_object* v_cache_661_; lean_object* v_transientCache_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_672_; 
v___x_659_ = lean_st_ref_take(v___y_643_);
v_numSteps_660_ = lean_ctor_get(v___x_659_, 0);
v_cache_661_ = lean_ctor_get(v___x_659_, 1);
v_transientCache_662_ = lean_ctor_get(v___x_659_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_672_ == 0)
{
v___x_664_ = v___x_659_;
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_transientCache_662_);
lean_inc(v_cache_661_);
lean_inc(v_numSteps_660_);
lean_dec(v___x_659_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc_ref(v_r_642_);
v___x_666_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_transientCache_662_, v_e_u2081_630_, v_r_642_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_numSteps_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_cache_661_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_st_ref_put(v___y_643_, v___x_668_);
lean_dec(v___y_643_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_r_642_);
return v___x_670_;
}
}
}
}
v___jp_673_:
{
lean_object* v___x_684_; 
lean_inc(v___y_677_);
lean_inc_ref(v_e_u2082_674_);
v___x_684_ = lean_sym_dsimp(v_e_u2082_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v_a_685_) == 0)
{
uint8_t v_done_686_; lean_object* v___x_687_; 
v_done_686_ = lean_ctor_get_uint8(v_a_685_, 0);
lean_dec_ref_known(v_a_685_, 0);
v___x_687_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_687_, 0, v_e_u2082_674_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*1, v_done_686_);
v_r_642_ = v___x_687_;
v___y_643_ = v___y_677_;
goto v___jp_641_;
}
else
{
lean_dec_ref(v_e_u2082_674_);
v_r_642_ = v_a_685_;
v___y_643_ = v___y_677_;
goto v___jp_641_;
}
}
else
{
lean_dec(v___y_677_);
lean_dec_ref(v_e_u2082_674_);
lean_dec_ref(v_e_u2081_630_);
return v___x_684_;
}
}
v___jp_688_:
{
if (v_done_700_ == 0)
{
lean_dec_ref(v_a_698_);
v_e_u2082_674_ = v_e_x27_699_;
v___y_675_ = v___y_697_;
v___y_676_ = v___y_696_;
v___y_677_ = v___y_695_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_689_;
v___y_680_ = v___y_691_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_693_;
v___y_683_ = v___y_692_;
goto v___jp_673_;
}
else
{
lean_dec_ref(v_e_x27_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
v_r_642_ = v_a_698_;
v___y_643_ = v___y_695_;
goto v___jp_641_;
}
}
v_resetjp_708_:
{
lean_object* v_maxRecDepth_711_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_maxRecDepth_711_ = lean_ctor_get(v_toCold_701_, 3);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_nat_dec_eq(v_maxRecDepth_711_, v___x_836_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_eq(v_currRecDepth_702_, v_maxRecDepth_711_);
if (v___x_838_ == 0)
{
goto v___jp_816_;
}
else
{
lean_object* v___x_839_; 
lean_del_object(v___x_709_);
lean_dec(v_currRecDepth_702_);
lean_dec_ref(v_toCold_701_);
lean_dec(v_a_639_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_u2081_630_);
v___x_839_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_703_);
return v___x_839_;
}
}
else
{
goto v___jp_816_;
}
v___jp_712_:
{
lean_object* v___x_723_; lean_object* v_cache_724_; lean_object* v_transientCache_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_761_; 
v___x_723_ = lean_st_ref_take(v___y_716_);
v_cache_724_ = lean_ctor_get(v___x_723_, 1);
v_transientCache_725_ = lean_ctor_get(v___x_723_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_762_);
v___x_727_ = v___x_723_;
v_isShared_728_ = v_isSharedCheck_761_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_transientCache_725_);
lean_inc(v_cache_724_);
lean_dec(v___x_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_761_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___y_713_);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___y_713_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_cache_724_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_transientCache_725_);
v___x_730_ = v_reuseFailAlloc_760_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v_pre_732_; lean_object* v___x_733_; 
v___x_731_ = lean_st_ref_put(v___y_716_, v___x_730_);
v_pre_732_ = lean_ctor_get(v___y_714_, 0);
lean_inc_ref(v_pre_732_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v_e_u2081_630_);
v___x_733_ = lean_apply_11(v_pre_732_, v_e_u2081_630_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
if (lean_obj_tag(v_a_734_) == 0)
{
uint8_t v_done_735_; 
v_done_735_ = lean_ctor_get_uint8(v_a_734_, 0);
if (v_done_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref_known(v_a_734_, 0);
v___x_736_ = lean_box(0);
lean_inc_ref(v_e_u2081_630_);
v___x_737_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_630_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
if (lean_obj_tag(v_a_738_) == 0)
{
uint8_t v_done_739_; 
v_done_739_ = lean_ctor_get_uint8(v_a_738_, 0);
if (v_done_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref_known(v_a_738_, 0);
lean_inc_ref(v_e_u2081_630_);
v___x_740_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_736_, v_e_u2081_630_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
if (lean_obj_tag(v_a_741_) == 0)
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_r_642_ = v_a_741_;
v___y_643_ = v___y_716_;
goto v___jp_641_;
}
else
{
lean_object* v_e_x27_742_; uint8_t v_done_743_; 
v_e_x27_742_ = lean_ctor_get(v_a_741_, 0);
lean_inc_ref(v_e_x27_742_);
v_done_743_ = lean_ctor_get_uint8(v_a_741_, sizeof(void*)*1);
v___y_689_ = v___y_718_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
v___y_693_ = v___y_721_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_716_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_714_;
v_a_698_ = v_a_741_;
v_e_x27_699_ = v_e_x27_742_;
v_done_700_ = v_done_743_;
goto v___jp_688_;
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_e_u2081_630_);
return v___x_740_;
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_r_642_ = v_a_738_;
v___y_643_ = v___y_716_;
goto v___jp_641_;
}
}
else
{
uint8_t v_done_744_; 
v_done_744_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*1);
if (v_done_744_ == 0)
{
lean_object* v_e_x27_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v_e_x27_745_ = lean_ctor_get(v_a_738_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v_a_738_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_e_x27_745_);
lean_dec(v_a_738_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; 
lean_inc_ref(v_e_x27_745_);
v___x_749_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_736_, v_e_x27_745_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
if (lean_obj_tag(v_a_750_) == 0)
{
uint8_t v_done_751_; lean_object* v___x_753_; 
v_done_751_ = lean_ctor_get_uint8(v_a_750_, 0);
lean_dec_ref_known(v_a_750_, 0);
lean_inc_ref(v_e_x27_745_);
if (v_isShared_748_ == 0)
{
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_e_x27_745_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v_done_751_);
v___y_689_ = v___y_718_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
v___y_693_ = v___y_721_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_716_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_714_;
v_a_698_ = v___x_753_;
v_e_x27_699_ = v_e_x27_745_;
v_done_700_ = v_done_751_;
goto v___jp_688_;
}
}
else
{
lean_object* v_e_x27_755_; uint8_t v_done_756_; 
lean_del_object(v___x_747_);
lean_dec_ref(v_e_x27_745_);
v_e_x27_755_ = lean_ctor_get(v_a_750_, 0);
lean_inc_ref(v_e_x27_755_);
v_done_756_ = lean_ctor_get_uint8(v_a_750_, sizeof(void*)*1);
v___y_689_ = v___y_718_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
v___y_693_ = v___y_721_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_716_;
v___y_696_ = v___y_715_;
v___y_697_ = v___y_714_;
v_a_698_ = v_a_750_;
v_e_x27_699_ = v_e_x27_755_;
v_done_700_ = v_done_756_;
goto v___jp_688_;
}
}
else
{
lean_del_object(v___x_747_);
lean_dec_ref(v_e_x27_745_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_e_u2081_630_);
return v___x_749_;
}
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_r_642_ = v_a_738_;
v___y_643_ = v___y_716_;
goto v___jp_641_;
}
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_e_u2081_630_);
return v___x_737_;
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_r_642_ = v_a_734_;
v___y_643_ = v___y_716_;
goto v___jp_641_;
}
}
else
{
uint8_t v_done_758_; 
v_done_758_ = lean_ctor_get_uint8(v_a_734_, sizeof(void*)*1);
if (v_done_758_ == 0)
{
lean_object* v_e_x27_759_; 
v_e_x27_759_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_e_x27_759_);
lean_dec_ref_known(v_a_734_, 1);
v_e_u2082_674_ = v_e_x27_759_;
v___y_675_ = v___y_714_;
v___y_676_ = v___y_715_;
v___y_677_ = v___y_716_;
v___y_678_ = v___y_717_;
v___y_679_ = v___y_718_;
v___y_680_ = v___y_719_;
v___y_681_ = v___y_720_;
v___y_682_ = v___y_721_;
v___y_683_ = v___y_722_;
goto v___jp_673_;
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
v_r_642_ = v_a_734_;
v___y_643_ = v___y_716_;
goto v___jp_641_;
}
}
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_e_u2081_630_);
return v___x_733_;
}
}
}
}
v___jp_763_:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v___y_775_, v_e_u2081_630_);
lean_dec_ref(v___y_775_);
if (lean_obj_tag(v___x_776_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v___y_774_);
lean_dec(v___y_773_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
lean_dec(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_e_u2081_630_);
v_val_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_val_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
lean_dec(v___x_776_);
v___x_785_ = lean_nat_add(v___y_773_, v___y_767_);
lean_dec(v___y_773_);
v___x_786_ = lean_unsigned_to_nat(1000u);
v___x_787_ = lean_nat_mod(v___x_785_, v___x_786_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_nat_dec_eq(v___x_787_, v___x_788_);
lean_dec(v___x_787_);
if (v___x_789_ == 0)
{
v___y_713_ = v___x_785_;
v___y_714_ = v___y_774_;
v___y_715_ = v___y_765_;
v___y_716_ = v___y_769_;
v___y_717_ = v___y_768_;
v___y_718_ = v___y_772_;
v___y_719_ = v___y_766_;
v___y_720_ = v___y_771_;
v___y_721_ = v___y_764_;
v___y_722_ = v___y_770_;
goto v___jp_712_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0));
v___x_791_ = l_Lean_Core_checkSystem(v___x_790_, v___y_764_, v___y_770_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
v___y_713_ = v___x_785_;
v___y_714_ = v___y_774_;
v___y_715_ = v___y_765_;
v___y_716_ = v___y_769_;
v___y_717_ = v___y_768_;
v___y_718_ = v___y_772_;
v___y_719_ = v___y_766_;
v___y_720_ = v___y_771_;
v___y_721_ = v___y_764_;
v___y_722_ = v___y_770_;
goto v___jp_712_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v___x_785_);
lean_dec(v___y_774_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
lean_dec(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_e_u2081_630_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
v___jp_800_:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_st_ref_get(v___y_805_);
v___x_813_ = l_Lean_Expr_hasMVar(v_e_u2081_630_);
if (v___x_813_ == 0)
{
lean_object* v_cache_814_; 
v_cache_814_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_cache_814_);
lean_dec(v___x_812_);
v___y_764_ = v___y_810_;
v___y_765_ = v___y_804_;
v___y_766_ = v___y_808_;
v___y_767_ = v___y_801_;
v___y_768_ = v___y_806_;
v___y_769_ = v___y_805_;
v___y_770_ = v___y_811_;
v___y_771_ = v___y_809_;
v___y_772_ = v___y_807_;
v___y_773_ = v___y_802_;
v___y_774_ = v___y_803_;
v___y_775_ = v_cache_814_;
goto v___jp_763_;
}
else
{
lean_object* v_transientCache_815_; 
v_transientCache_815_ = lean_ctor_get(v___x_812_, 2);
lean_inc_ref(v_transientCache_815_);
lean_dec(v___x_812_);
v___y_764_ = v___y_810_;
v___y_765_ = v___y_804_;
v___y_766_ = v___y_808_;
v___y_767_ = v___y_801_;
v___y_768_ = v___y_806_;
v___y_769_ = v___y_805_;
v___y_770_ = v___y_811_;
v___y_771_ = v___y_809_;
v___y_772_ = v___y_807_;
v___y_773_ = v___y_802_;
v___y_774_ = v___y_803_;
v___y_775_ = v_transientCache_815_;
goto v___jp_763_;
}
}
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_currRecDepth_702_, v___x_817_);
lean_dec(v_currRecDepth_702_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_818_);
v___x_820_ = v___x_709_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_toCold_701_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ref_703_);
lean_ctor_set_uint16(v_reuseFailAlloc_835_, sizeof(void*)*3, v_optionFlags_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3 + 2, v_suppressElabErrors_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3 + 3, v_checkDeprecated_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3 + 4, v_isRecordingDeps_707_);
v___x_820_ = v_reuseFailAlloc_835_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v_numSteps_822_; lean_object* v_maxSteps_823_; uint8_t v___x_824_; 
v___x_821_ = lean_st_ref_get(v_a_633_);
v_numSteps_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_numSteps_822_);
lean_dec(v___x_821_);
v_maxSteps_823_ = lean_ctor_get(v_a_632_, 0);
v___x_824_ = lean_nat_dec_le(v_maxSteps_823_, v_numSteps_822_);
if (v___x_824_ == 0)
{
v___y_801_ = v___x_817_;
v___y_802_ = v_numSteps_822_;
v___y_803_ = v_a_631_;
v___y_804_ = v_a_632_;
v___y_805_ = v_a_633_;
v___y_806_ = v_a_634_;
v___y_807_ = v_a_635_;
v___y_808_ = v_a_636_;
v___y_809_ = v_a_637_;
v___y_810_ = v___x_820_;
v___y_811_ = v_a_639_;
goto v___jp_800_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_numSteps_822_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_u2081_630_);
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
v___x_826_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_825_, v_a_636_, v_a_637_, v___x_820_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v___x_820_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object* v_e_u2081_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = lean_sym_dsimp(v_e_u2081_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object* v_00_u03b2_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_854_, v_x_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_862_, v_x_863_, v_x_864_);
lean_dec_ref(v_x_864_);
lean_dec_ref(v_x_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, size_t v_x_868_, size_t v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
size_t v_x_45624__boxed_879_; size_t v_x_45625__boxed_880_; lean_object* v_res_881_; 
v_x_45624__boxed_879_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_x_45625__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_res_881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_873_, v_x_874_, v_x_45624__boxed_879_, v_x_45625__boxed_880_, v_x_877_, v_x_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, size_t v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_883_, v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
size_t v_x_45641__boxed_891_; lean_object* v_res_892_; 
v_x_45641__boxed_891_ = lean_unbox_usize(v_x_889_);
lean_dec(v_x_889_);
v_res_892_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_887_, v_x_888_, v_x_45641__boxed_891_, v_x_890_);
lean_dec_ref(v_x_890_);
lean_dec_ref(v_x_888_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_893_, lean_object* v_n_894_, lean_object* v_k_895_, lean_object* v_v_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_894_, v_k_895_, v_v_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_898_, size_t v_depth_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_entries_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_899_, v_keys_900_, v_vals_901_, v_i_903_, v_entries_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_906_, lean_object* v_depth_907_, lean_object* v_keys_908_, lean_object* v_vals_909_, lean_object* v_heq_910_, lean_object* v_i_911_, lean_object* v_entries_912_){
_start:
{
size_t v_depth_boxed_913_; lean_object* v_res_914_; 
v_depth_boxed_913_ = lean_unbox_usize(v_depth_907_);
lean_dec(v_depth_907_);
v_res_914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_906_, v_depth_boxed_913_, v_keys_908_, v_vals_909_, v_heq_910_, v_i_911_, v_entries_912_);
lean_dec_ref(v_vals_909_);
lean_dec_ref(v_keys_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_heq_918_, lean_object* v_i_919_, lean_object* v_k_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_916_, v_vals_917_, v_i_919_, v_k_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_k_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_922_, v_keys_923_, v_vals_924_, v_heq_925_, v_i_926_, v_k_927_);
lean_dec_ref(v_k_927_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_930_, v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
