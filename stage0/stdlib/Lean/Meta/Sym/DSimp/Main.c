// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Main
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.DSimproc import Lean.Meta.Sym.DSimp.App import Lean.Meta.Sym.DSimp.Lambda import Lean.Meta.Sym.DSimp.Forall import Lean.Meta.Sym.DSimp.Let import Lean.Meta.Sym.AlphaShareBuilder
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
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(lean_object* v_d_1_, lean_object* v_e_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*12);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_1_, v_e_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg___boxed(lean_object* v_d_26_, lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_26_, v_e_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_35_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(lean_object* v_d_36_, lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_d_36_, v_e_37_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
return v___x_48_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_36_ = stack[0].m_obj;
lean_object* v_e_37_ = stack[1].m_obj;
lean_object* v___y_38_ = stack[2].m_obj;
lean_object* v___y_39_ = stack[3].m_obj;
lean_object* v___y_40_ = stack[4].m_obj;
lean_object* v___y_41_ = stack[5].m_obj;
lean_object* v___y_42_ = stack[6].m_obj;
lean_object* v___y_43_ = stack[7].m_obj;
lean_object* v___y_44_ = stack[8].m_obj;
lean_object* v___y_45_ = stack[9].m_obj;
lean_object* v___y_46_ = stack[10].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_36_, v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___boxed(lean_object* v_d_50_, lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0(v_d_50_, v_e_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
return v_res_62_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(lean_object* v_msgData_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_env_70_; uint8_t v___x_71_; lean_object* v_env_72_; lean_object* v___x_73_; lean_object* v_toCold_74_; lean_object* v_mctx_75_; lean_object* v_lctx_76_; lean_object* v_options_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_69_ = lean_st_ref_get(v___y_67_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = 0;
v_env_72_ = l_Lean_Environment_setRecordingDeps(v_env_70_, v___x_71_);
v___x_73_ = lean_st_ref_get(v___y_65_);
v_toCold_74_ = lean_ctor_get(v___y_66_, 0);
v_mctx_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_mctx_75_);
lean_dec(v___x_73_);
v_lctx_76_ = lean_ctor_get(v___y_64_, 2);
v_options_77_ = lean_ctor_get(v_toCold_74_, 2);
lean_inc_ref(v_options_77_);
lean_inc_ref(v_lctx_76_);
v___x_78_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_78_, 0, v_env_72_);
lean_ctor_set(v___x_78_, 1, v_mctx_75_);
lean_ctor_set(v___x_78_, 2, v_lctx_76_);
lean_ctor_set(v___x_78_, 3, v_options_77_);
v___x_79_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_msgData_63_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_63_ = stack[0].m_obj;
lean_object* v___y_64_ = stack[1].m_obj;
lean_object* v___y_65_ = stack[2].m_obj;
lean_object* v___y_66_ = stack[3].m_obj;
lean_object* v___y_67_ = stack[4].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_88_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_ref_95_; lean_object* v___x_96_; lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_ref_95_ = lean_ctor_get(v___y_92_, 2);
v___x_96_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
lean_inc(v_ref_95_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_ref_95_);
lean_ctor_set(v___x_101_, 1, v_a_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 1);
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_89_ = stack[0].m_obj;
lean_object* v___y_90_ = stack[1].m_obj;
lean_object* v___y_91_ = stack[2].m_obj;
lean_object* v___y_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1));
v___x_118_ = l_Lean_stringToMessageData(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3));
v___x_121_ = l_Lean_stringToMessageData(v___x_120_);
return v___x_121_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object* v_e_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_a_134_; 
switch(lean_obj_tag(v_e_122_))
{
case 5:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_138_;
}
case 6:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_139_;
}
case 7:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_140_;
}
case 8:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_141_;
}
case 10:
{
lean_object* v_data_142_; lean_object* v_expr_143_; lean_object* v___x_144_; 
v_data_142_ = lean_ctor_get(v_e_122_, 0);
v_expr_143_ = lean_ctor_get(v_e_122_, 1);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_a_129_);
lean_inc_ref(v_a_128_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_expr_143_);
v___x_144_ = lean_sym_dsimp(v_expr_143_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_167_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_167_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
if (lean_obj_tag(v_a_145_) == 0)
{
lean_object* v___x_149_; lean_object* v___x_151_; 
lean_dec_ref_known(v_a_145_, 0);
lean_dec_ref_known(v_e_122_, 2);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
else
{
lean_object* v_e_x27_153_; size_t v___x_154_; size_t v___x_155_; uint8_t v___x_156_; 
lean_del_object(v___x_147_);
v_e_x27_153_ = lean_ctor_get(v_a_145_, 0);
lean_inc_ref(v_e_x27_153_);
lean_dec_ref_known(v_a_145_, 1);
v___x_154_ = lean_ptr_addr(v_expr_143_);
v___x_155_ = lean_ptr_addr(v_e_x27_153_);
v___x_156_ = lean_usize_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
lean_inc(v_data_142_);
lean_dec_ref_known(v_e_122_, 2);
v___x_157_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_142_, v_e_x27_153_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v_a_134_ = v_a_158_;
goto v___jp_133_;
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_157_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_153_);
v_a_134_ = v_e_122_;
goto v___jp_133_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_122_, 2);
return v___x_144_;
}
}
case 11:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
v___x_169_ = l_Lean_indentExpr(v_e_122_);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_172_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_173_;
}
default: 
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v_e_122_);
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
v___jp_133_:
{
uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = 0;
v___x_136_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_136_, 0, v_a_134_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_122_ = stack[0].m_obj;
lean_object* v_a_123_ = stack[1].m_obj;
lean_object* v_a_124_ = stack[2].m_obj;
lean_object* v_a_125_ = stack[3].m_obj;
lean_object* v_a_126_ = stack[4].m_obj;
lean_object* v_a_127_ = stack[5].m_obj;
lean_object* v_a_128_ = stack[6].m_obj;
lean_object* v_a_129_ = stack[7].m_obj;
lean_object* v_a_130_ = stack[8].m_obj;
lean_object* v_a_131_ = stack[9].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
return v_res_188_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object* v_00_u03b1_189_, lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_190_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_190_ = stack[1].m_obj;
lean_object* v___y_191_ = stack[2].m_obj;
lean_object* v___y_192_ = stack[3].m_obj;
lean_object* v___y_193_ = stack[4].m_obj;
lean_object* v___y_194_ = stack[5].m_obj;
lean_object* v___y_195_ = stack[6].m_obj;
lean_object* v___y_196_ = stack[7].m_obj;
lean_object* v___y_197_ = stack[8].m_obj;
lean_object* v___y_198_ = stack[9].m_obj;
lean_object* v___y_199_ = stack[10].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_box(0), v_msg_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object* v_00_u03b1_203_, lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_203_, v_msg_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
return v_res_215_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object* v_e_218_, lean_object* v_r_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v_numSteps_225_; lean_object* v_cache_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_236_; 
v___f_222_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_223_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
v___x_224_ = lean_st_ref_take(v_a_220_);
v_numSteps_225_ = lean_ctor_get(v___x_224_, 0);
v_cache_226_ = lean_ctor_get(v___x_224_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_236_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_236_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_cache_226_);
lean_inc(v_numSteps_225_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_236_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_inc_ref(v_r_219_);
v___x_230_ = l_Lean_PersistentHashMap_insert___redArg(v___f_222_, v___f_223_, v_cache_226_, v_e_218_, v_r_219_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_numSteps_225_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_st_ref_put(v_a_220_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_r_219_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_218_ = stack[0].m_obj;
lean_object* v_r_219_ = stack[1].m_obj;
lean_object* v_a_220_ = stack[2].m_obj;
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(v_e_218_, v_r_219_, v_a_220_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object* v_e_238_, lean_object* v_r_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(v_e_238_, v_r_239_, v_a_240_);
lean_dec(v_a_240_);
return v_res_242_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object* v_e_243_, lean_object* v_r_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v_numSteps_258_; lean_object* v_cache_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v___f_255_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_256_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
v___x_257_ = lean_st_ref_take(v_a_247_);
v_numSteps_258_ = lean_ctor_get(v___x_257_, 0);
v_cache_259_ = lean_ctor_get(v___x_257_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_cache_259_);
lean_inc(v_numSteps_258_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_inc_ref(v_r_244_);
v___x_263_ = l_Lean_PersistentHashMap_insert___redArg(v___f_255_, v___f_256_, v_cache_259_, v_e_243_, v_r_244_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_numSteps_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_268_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_st_ref_put(v_a_247_, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_r_244_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_243_ = stack[0].m_obj;
lean_object* v_r_244_ = stack[1].m_obj;
lean_object* v_a_245_ = stack[2].m_obj;
lean_object* v_a_246_ = stack[3].m_obj;
lean_object* v_a_247_ = stack[4].m_obj;
lean_object* v_a_248_ = stack[5].m_obj;
lean_object* v_a_249_ = stack[6].m_obj;
lean_object* v_a_250_ = stack[7].m_obj;
lean_object* v_a_251_ = stack[8].m_obj;
lean_object* v_a_252_ = stack[9].m_obj;
lean_object* v_a_253_ = stack[10].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(v_e_243_, v_r_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object* v_e_271_, lean_object* v_r_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(v_e_271_, v_r_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
return v_res_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = l_Lean_maxRecDepthErrorMessage;
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
v___x_292_ = l_Lean_MessageData_ofFormat(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
v___x_294_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2));
v___x_295_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object* v_ref_296_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_296_ = stack[0].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_296_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object* v_ref_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_302_);
return v_res_304_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object* v_00_u03b1_305_, lean_object* v_ref_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_306_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v___y_310_ = stack[5].m_obj;
lean_object* v___y_311_ = stack[6].m_obj;
lean_object* v___y_312_ = stack[7].m_obj;
lean_object* v___y_313_ = stack[8].m_obj;
lean_object* v___y_314_ = stack[9].m_obj;
lean_object* v___y_315_ = stack[10].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_box(0), v_ref_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object* v_00_u03b1_319_, lean_object* v_ref_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_319_, v_ref_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
return v_res_331_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_post_344_; lean_object* v___x_345_; 
v_post_344_ = lean_ctor_get(v___y_334_, 1);
lean_inc_ref(v_post_344_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
lean_inc(v___y_340_);
lean_inc_ref(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
v___x_345_ = lean_apply_11(v_post_344_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, lean_box(0));
return v___x_345_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_332_ = stack[0].m_obj;
lean_object* v___y_333_ = stack[1].m_obj;
lean_object* v___y_334_ = stack[2].m_obj;
lean_object* v___y_335_ = stack[3].m_obj;
lean_object* v___y_336_ = stack[4].m_obj;
lean_object* v___y_337_ = stack[5].m_obj;
lean_object* v___y_338_ = stack[6].m_obj;
lean_object* v___y_339_ = stack[7].m_obj;
lean_object* v___y_340_ = stack[8].m_obj;
lean_object* v___y_341_ = stack[9].m_obj;
lean_object* v___y_342_ = stack[10].m_obj;
lean_object* v_res_346_;
v_res_346_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object* v_x_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v_x_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_ks_364_; lean_object* v_vs_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_391_; 
v_ks_364_ = lean_ctor_get(v_x_360_, 0);
v_vs_365_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_391_ == 0)
{
v___x_367_ = v_x_360_;
v_isShared_368_ = v_isSharedCheck_391_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_vs_365_);
lean_inc(v_ks_364_);
lean_dec(v_x_360_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_391_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_array_get_size(v_ks_364_);
v___x_370_ = lean_nat_dec_lt(v_x_361_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec(v_x_361_);
v___x_371_ = lean_array_push(v_ks_364_, v_x_362_);
v___x_372_ = lean_array_push(v_vs_365_, v_x_363_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_372_);
lean_ctor_set(v___x_367_, 0, v___x_371_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v_k_x27_376_; size_t v___x_377_; size_t v___x_378_; uint8_t v___x_379_; 
v_k_x27_376_ = lean_array_fget_borrowed(v_ks_364_, v_x_361_);
v___x_377_ = lean_ptr_addr(v_x_362_);
v___x_378_ = lean_ptr_addr(v_k_x27_376_);
v___x_379_ = lean_usize_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_381_; 
if (v_isShared_368_ == 0)
{
v___x_381_ = v___x_367_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_ks_364_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_vs_365_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_x_361_, v___x_382_);
lean_dec(v_x_361_);
v_x_360_ = v___x_381_;
v_x_361_ = v___x_383_;
goto _start;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = lean_array_fset(v_ks_364_, v_x_361_, v_x_362_);
v___x_387_ = lean_array_fset(v_vs_365_, v_x_361_, v_x_363_);
lean_dec(v_x_361_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_387_);
lean_ctor_set(v___x_367_, 0, v___x_386_);
v___x_389_ = v___x_367_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_392_, lean_object* v_k_393_, lean_object* v_v_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_392_, v___x_395_, v_k_393_, v_v_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_397_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object* v_x_398_, size_t v_x_399_, size_t v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_es_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v_j_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_es_403_ = lean_ctor_get(v_x_398_, 0);
v___x_404_ = ((size_t)31ULL);
v___x_405_ = lean_usize_land(v_x_399_, v___x_404_);
v_j_406_ = lean_usize_to_nat(v___x_405_);
v___x_407_ = lean_array_get_size(v_es_403_);
v___x_408_ = lean_nat_dec_lt(v_j_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_j_406_);
lean_dec(v_x_402_);
lean_dec_ref(v_x_401_);
return v_x_398_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_449_; 
lean_inc_ref(v_es_403_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_450_);
v___x_410_ = v_x_398_;
v_isShared_411_ = v_isSharedCheck_449_;
goto v_resetjp_409_;
}
else
{
lean_dec(v_x_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_449_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_xs_x27_414_; lean_object* v___y_416_; 
v_v_412_ = lean_array_fget(v_es_403_, v_j_406_);
v___x_413_ = lean_box(0);
v_xs_x27_414_ = lean_array_fset(v_es_403_, v_j_406_, v___x_413_);
switch(lean_obj_tag(v_v_412_))
{
case 0:
{
lean_object* v_key_421_; lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_434_; 
v_key_421_ = lean_ctor_get(v_v_412_, 0);
v_val_422_ = lean_ctor_get(v_v_412_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_434_ == 0)
{
v___x_424_ = v_v_412_;
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_inc(v_key_421_);
lean_dec(v_v_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
size_t v___x_426_; size_t v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_ptr_addr(v_x_401_);
v___x_427_ = lean_ptr_addr(v_key_421_);
v___x_428_ = lean_usize_dec_eq(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_del_object(v___x_424_);
v___x_429_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_421_, v_val_422_, v_x_401_, v_x_402_);
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
v___y_416_ = v___x_430_;
goto v___jp_415_;
}
else
{
lean_object* v___x_432_; 
lean_dec(v_val_422_);
lean_dec(v_key_421_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v_x_402_);
lean_ctor_set(v___x_424_, 0, v_x_401_);
v___x_432_ = v___x_424_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_x_402_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v___y_416_ = v___x_432_;
goto v___jp_415_;
}
}
}
}
case 1:
{
lean_object* v_node_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_447_; 
v_node_435_ = lean_ctor_get(v_v_412_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_447_ == 0)
{
v___x_437_ = v_v_412_;
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_node_435_);
lean_dec(v_v_412_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_usize_shift_right(v_x_399_, v___x_439_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_x_400_, v___x_441_);
v___x_443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_node_435_, v___x_440_, v___x_442_, v_x_401_, v_x_402_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_443_);
v___x_445_ = v___x_437_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v___y_416_ = v___x_445_;
goto v___jp_415_;
}
}
}
default: 
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_x_401_);
lean_ctor_set(v___x_448_, 1, v_x_402_);
v___y_416_ = v___x_448_;
goto v___jp_415_;
}
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_array_fset(v_xs_x27_414_, v_j_406_, v___y_416_);
lean_dec(v_j_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_417_);
v___x_419_ = v___x_410_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v_ks_451_; lean_object* v_vs_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_470_; 
v_ks_451_ = lean_ctor_get(v_x_398_, 0);
v_vs_452_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_470_ == 0)
{
v___x_454_ = v_x_398_;
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_vs_452_);
lean_inc(v_ks_451_);
lean_dec(v_x_398_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ks_451_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_vs_452_);
v___x_457_ = v_reuseFailAlloc_469_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v_newNode_458_; size_t v___x_459_; uint8_t v___x_460_; 
v_newNode_458_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v___x_457_, v_x_401_, v_x_402_);
v___x_459_ = ((size_t)7ULL);
v___x_460_ = lean_usize_dec_le(v___x_459_, v_x_400_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_458_);
v___x_462_ = lean_unsigned_to_nat(4u);
v___x_463_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
lean_dec(v___x_461_);
if (v___x_463_ == 0)
{
lean_object* v_ks_464_; lean_object* v_vs_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_ks_464_ = lean_ctor_get(v_newNode_458_, 0);
lean_inc_ref(v_ks_464_);
v_vs_465_ = lean_ctor_get(v_newNode_458_, 1);
lean_inc_ref(v_vs_465_);
lean_dec_ref(v_newNode_458_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
v___x_468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_400_, v_ks_464_, v_vs_465_, v___x_466_, v___x_467_);
lean_dec_ref(v_vs_465_);
lean_dec_ref(v_ks_464_);
return v___x_468_;
}
else
{
return v_newNode_458_;
}
}
else
{
return v_newNode_458_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_398_ = stack[0].m_obj;
size_t v_x_399_ = stack[1].m_num;
size_t v_x_400_ = stack[2].m_num;
lean_object* v_x_401_ = stack[3].m_obj;
lean_object* v_x_402_ = stack[4].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_398_, v_x_399_, v_x_400_, v_x_401_, v_x_402_);
stack->m_obj
 = v_res_471_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_472_, lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_array_get_size(v_keys_473_);
v___x_478_ = lean_nat_dec_lt(v_i_475_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v_i_475_);
return v_entries_476_;
}
else
{
lean_object* v_k_479_; lean_object* v_v_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; uint64_t v___x_484_; size_t v_h_485_; size_t v___x_486_; lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v_h_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_k_479_ = lean_array_fget_borrowed(v_keys_473_, v_i_475_);
v_v_480_ = lean_array_fget_borrowed(v_vals_474_, v_i_475_);
v___x_481_ = lean_ptr_addr(v_k_479_);
v___x_482_ = ((size_t)3ULL);
v___x_483_ = lean_usize_shift_right(v___x_481_, v___x_482_);
v___x_484_ = lean_usize_to_uint64(v___x_483_);
v_h_485_ = lean_uint64_to_usize(v___x_484_);
v___x_486_ = ((size_t)5ULL);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_sub(v_depth_472_, v___x_488_);
v___x_490_ = lean_usize_mul(v___x_486_, v___x_489_);
v_h_491_ = lean_usize_shift_right(v_h_485_, v___x_490_);
v___x_492_ = lean_nat_add(v_i_475_, v___x_487_);
lean_dec(v_i_475_);
lean_inc(v_v_480_);
lean_inc(v_k_479_);
v___x_493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_entries_476_, v_h_491_, v_depth_472_, v_k_479_, v_v_480_);
v_i_475_ = v___x_492_;
v_entries_476_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_472_ = stack[0].m_num;
lean_object* v_keys_473_ = stack[1].m_obj;
lean_object* v_vals_474_ = stack[2].m_obj;
lean_object* v_i_475_ = stack[3].m_obj;
lean_object* v_entries_476_ = stack[4].m_obj;
lean_object* v_res_495_;
v_res_495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_472_, v_keys_473_, v_vals_474_, v_i_475_, v_entries_476_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_i_499_, lean_object* v_entries_500_){
_start:
{
size_t v_depth_boxed_501_; lean_object* v_res_502_; 
v_depth_boxed_501_ = lean_unbox_usize(v_depth_496_);
lean_dec(v_depth_496_);
v_res_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_501_, v_keys_497_, v_vals_498_, v_i_499_, v_entries_500_);
lean_dec_ref(v_vals_498_);
lean_dec_ref(v_keys_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
size_t v_x_41830__boxed_508_; size_t v_x_41831__boxed_509_; lean_object* v_res_510_; 
v_x_41830__boxed_508_ = lean_unbox_usize(v_x_504_);
lean_dec(v_x_504_);
v_x_41831__boxed_509_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_res_510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_503_, v_x_41830__boxed_508_, v_x_41831__boxed_509_, v_x_506_, v_x_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_514_ = lean_ptr_addr(v_x_512_);
v___x_515_ = ((size_t)3ULL);
v___x_516_ = lean_usize_shift_right(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_to_uint64(v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_511_, v___x_518_, v___x_519_, v_x_512_, v_x_513_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_521_, lean_object* v_vals_522_, lean_object* v_i_523_, lean_object* v_k_524_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_keys_521_);
v___x_526_ = lean_nat_dec_lt(v_i_523_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v_i_523_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v_k_x27_528_; size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; 
v_k_x27_528_ = lean_array_fget_borrowed(v_keys_521_, v_i_523_);
v___x_529_ = lean_ptr_addr(v_k_524_);
v___x_530_ = lean_ptr_addr(v_k_x27_528_);
v___x_531_ = lean_usize_dec_eq(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_i_523_, v___x_532_);
lean_dec(v_i_523_);
v_i_523_ = v___x_533_;
goto _start;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_array_fget_borrowed(v_vals_522_, v_i_523_);
lean_dec(v_i_523_);
lean_inc(v___x_535_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_i_539_, lean_object* v_k_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_537_, v_vals_538_, v_i_539_, v_k_540_);
lean_dec_ref(v_k_540_);
lean_dec_ref(v_vals_538_);
lean_dec_ref(v_keys_537_);
return v_res_541_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object* v_x_542_, size_t v_x_543_, lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
lean_object* v_es_545_; lean_object* v___x_546_; size_t v___x_547_; size_t v___x_548_; lean_object* v_j_549_; lean_object* v___x_550_; 
v_es_545_ = lean_ctor_get(v_x_542_, 0);
v___x_546_ = lean_box(2);
v___x_547_ = ((size_t)31ULL);
v___x_548_ = lean_usize_land(v_x_543_, v___x_547_);
v_j_549_ = lean_usize_to_nat(v___x_548_);
v___x_550_ = lean_array_get_borrowed(v___x_546_, v_es_545_, v_j_549_);
lean_dec(v_j_549_);
switch(lean_obj_tag(v___x_550_))
{
case 0:
{
lean_object* v_key_551_; lean_object* v_val_552_; size_t v___x_553_; size_t v___x_554_; uint8_t v___x_555_; 
v_key_551_ = lean_ctor_get(v___x_550_, 0);
v_val_552_ = lean_ctor_get(v___x_550_, 1);
v___x_553_ = lean_ptr_addr(v_x_544_);
v___x_554_ = lean_ptr_addr(v_key_551_);
v___x_555_ = lean_usize_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
lean_inc(v_val_552_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_val_552_);
return v___x_557_;
}
}
case 1:
{
lean_object* v_node_558_; size_t v___x_559_; size_t v___x_560_; 
v_node_558_ = lean_ctor_get(v___x_550_, 0);
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_usize_shift_right(v_x_543_, v___x_559_);
v_x_542_ = v_node_558_;
v_x_543_ = v___x_560_;
goto _start;
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
}
else
{
lean_object* v_ks_563_; lean_object* v_vs_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_ks_563_ = lean_ctor_get(v_x_542_, 0);
v_vs_564_ = lean_ctor_get(v_x_542_, 1);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_563_, v_vs_564_, v___x_565_, v_x_544_);
return v___x_566_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_542_ = stack[0].m_obj;
size_t v_x_543_ = stack[1].m_num;
lean_object* v_x_544_ = stack[2].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_542_, v_x_543_, v_x_544_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
size_t v_x_42141__boxed_571_; lean_object* v_res_572_; 
v_x_42141__boxed_571_ = lean_unbox_usize(v_x_569_);
lean_dec(v_x_569_);
v_res_572_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_568_, v_x_42141__boxed_571_, v_x_570_);
lean_dec_ref(v_x_570_);
lean_dec_ref(v_x_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; uint64_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_575_ = lean_ptr_addr(v_x_574_);
v___x_576_ = ((size_t)3ULL);
v___x_577_ = lean_usize_shift_right(v___x_575_, v___x_576_);
v___x_578_ = lean_usize_to_uint64(v___x_577_);
v___x_579_ = lean_uint64_to_usize(v___x_578_);
v___x_580_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_573_, v___x_579_, v_x_574_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_581_, v_x_582_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_x_581_);
return v_res_583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
lean_object* lean_sym_dsimp(lean_object* v_e_u2081_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_r_600_; lean_object* v___y_601_; lean_object* v_e_u2082_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_a_640_; lean_object* v_e_x27_641_; uint8_t v_done_642_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v_toCold_657_; lean_object* v_currRecDepth_658_; lean_object* v_ref_659_; uint16_t v_optionFlags_660_; uint8_t v_suppressElabErrors_661_; uint8_t v_isRecordingDeps_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_776_; 
v_toCold_657_ = lean_ctor_get(v_a_596_, 0);
v_currRecDepth_658_ = lean_ctor_get(v_a_596_, 1);
v_ref_659_ = lean_ctor_get(v_a_596_, 2);
v_optionFlags_660_ = lean_ctor_get_uint16(v_a_596_, sizeof(void*)*3);
v_suppressElabErrors_661_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*3 + 2);
v_isRecordingDeps_662_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*3 + 3);
v_isSharedCheck_776_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_776_ == 0)
{
v___x_664_ = v_a_596_;
v_isShared_665_ = v_isSharedCheck_776_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_ref_659_);
lean_inc(v_currRecDepth_658_);
lean_inc(v_toCold_657_);
lean_dec(v_a_596_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_776_;
goto v_resetjp_663_;
}
v___jp_599_:
{
lean_object* v___x_602_; lean_object* v_numSteps_603_; lean_object* v_cache_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
v___x_602_ = lean_st_ref_take(v___y_601_);
v_numSteps_603_ = lean_ctor_get(v___x_602_, 0);
v_cache_604_ = lean_ctor_get(v___x_602_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_614_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_cache_604_);
lean_inc(v_numSteps_603_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
lean_inc_ref(v_r_600_);
v___x_608_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_604_, v_e_u2081_588_, v_r_600_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_numSteps_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_put(v___y_601_, v___x_610_);
lean_dec(v___y_601_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_r_600_);
return v___x_612_;
}
}
}
v___jp_615_:
{
lean_object* v___x_626_; 
lean_inc(v___y_619_);
lean_inc_ref(v_e_u2082_616_);
v___x_626_ = lean_sym_dsimp(v_e_u2082_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
if (lean_obj_tag(v_a_627_) == 0)
{
uint8_t v_done_628_; lean_object* v___x_629_; 
v_done_628_ = lean_ctor_get_uint8(v_a_627_, 0);
lean_dec_ref_known(v_a_627_, 0);
v___x_629_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_629_, 0, v_e_u2082_616_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v_done_628_);
v_r_600_ = v___x_629_;
v___y_601_ = v___y_619_;
goto v___jp_599_;
}
else
{
lean_dec_ref(v_e_u2082_616_);
v_r_600_ = v_a_627_;
v___y_601_ = v___y_619_;
goto v___jp_599_;
}
}
else
{
lean_dec(v___y_619_);
lean_dec_ref(v_e_u2082_616_);
lean_dec_ref(v_e_u2081_588_);
return v___x_626_;
}
}
v___jp_630_:
{
if (v_done_642_ == 0)
{
lean_dec_ref(v_a_640_);
v_e_u2082_616_ = v_e_x27_641_;
v___y_617_ = v___y_634_;
v___y_618_ = v___y_633_;
v___y_619_ = v___y_638_;
v___y_620_ = v___y_639_;
v___y_621_ = v___y_632_;
v___y_622_ = v___y_635_;
v___y_623_ = v___y_637_;
v___y_624_ = v___y_636_;
v___y_625_ = v___y_631_;
goto v___jp_615_;
}
else
{
lean_dec_ref(v_e_x27_641_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
v_r_600_ = v_a_640_;
v___y_601_ = v___y_638_;
goto v___jp_599_;
}
}
v___jp_643_:
{
if (lean_obj_tag(v___y_653_) == 0)
{
lean_object* v_a_654_; 
v_a_654_ = lean_ctor_get(v___y_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___y_653_, 1);
if (lean_obj_tag(v_a_654_) == 0)
{
lean_dec_ref(v___y_652_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
v_r_600_ = v_a_654_;
v___y_601_ = v___y_651_;
goto v___jp_599_;
}
else
{
lean_object* v_e_x27_655_; uint8_t v_done_656_; 
v_e_x27_655_ = lean_ctor_get(v_a_654_, 0);
lean_inc_ref(v_e_x27_655_);
v_done_656_ = lean_ctor_get_uint8(v_a_654_, sizeof(void*)*1);
v___y_631_ = v___y_647_;
v___y_632_ = v___y_646_;
v___y_633_ = v___y_645_;
v___y_634_ = v___y_644_;
v___y_635_ = v___y_648_;
v___y_636_ = v___y_649_;
v___y_637_ = v___y_650_;
v___y_638_ = v___y_651_;
v___y_639_ = v___y_652_;
v_a_640_ = v_a_654_;
v_e_x27_641_ = v_e_x27_655_;
v_done_642_ = v_done_656_;
goto v___jp_630_;
}
}
else
{
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v_e_u2081_588_);
return v___y_653_;
}
}
v_resetjp_663_:
{
lean_object* v_maxRecDepth_666_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_maxRecDepth_666_ = lean_ctor_get(v_toCold_657_, 3);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_nat_dec_eq(v_maxRecDepth_666_, v___x_772_);
if (v___x_773_ == 0)
{
uint8_t v___x_774_; 
v___x_774_ = lean_nat_dec_eq(v_currRecDepth_658_, v_maxRecDepth_666_);
if (v___x_774_ == 0)
{
goto v___jp_752_;
}
else
{
lean_object* v___x_775_; 
lean_del_object(v___x_664_);
lean_dec(v_currRecDepth_658_);
lean_dec_ref(v_toCold_657_);
lean_dec(v_a_597_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_e_u2081_588_);
v___x_775_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_659_);
return v___x_775_;
}
}
else
{
goto v___jp_752_;
}
v___jp_667_:
{
lean_object* v___x_678_; lean_object* v_cache_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_712_; 
v___x_678_ = lean_st_ref_take(v___y_671_);
v_cache_679_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_678_, 0);
lean_dec(v_unused_713_);
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_712_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_cache_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_712_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___y_668_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___y_668_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_cache_679_);
v___x_684_ = v_reuseFailAlloc_711_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v_pre_686_; lean_object* v___x_687_; 
v___x_685_ = lean_st_ref_put(v___y_671_, v___x_684_);
v_pre_686_ = lean_ctor_get(v___y_669_, 0);
lean_inc_ref(v_pre_686_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
lean_inc(v___y_669_);
lean_inc_ref(v_e_u2081_588_);
v___x_687_ = lean_apply_11(v_pre_686_, v_e_u2081_588_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
if (lean_obj_tag(v_a_688_) == 0)
{
uint8_t v_done_689_; 
v_done_689_ = lean_ctor_get_uint8(v_a_688_, 0);
if (v_done_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref_known(v_a_688_, 0);
v___x_690_ = lean_box(0);
lean_inc_ref(v_e_u2081_588_);
v___x_691_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_588_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
if (lean_obj_tag(v_a_692_) == 0)
{
uint8_t v_done_693_; 
v_done_693_ = lean_ctor_get_uint8(v_a_692_, 0);
lean_dec_ref_known(v_a_692_, 0);
if (v_done_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec_ref_known(v___x_691_, 1);
lean_inc_ref(v_e_u2081_588_);
v___x_694_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_690_, v_e_u2081_588_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
v___y_644_ = v___y_669_;
v___y_645_ = v___y_670_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_677_;
v___y_648_ = v___y_674_;
v___y_649_ = v___y_676_;
v___y_650_ = v___y_675_;
v___y_651_ = v___y_671_;
v___y_652_ = v___y_672_;
v___y_653_ = v___x_694_;
goto v___jp_643_;
}
else
{
v___y_644_ = v___y_669_;
v___y_645_ = v___y_670_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_677_;
v___y_648_ = v___y_674_;
v___y_649_ = v___y_676_;
v___y_650_ = v___y_675_;
v___y_651_ = v___y_671_;
v___y_652_ = v___y_672_;
v___y_653_ = v___x_691_;
goto v___jp_643_;
}
}
else
{
uint8_t v_done_695_; 
v_done_695_ = lean_ctor_get_uint8(v_a_692_, sizeof(void*)*1);
if (v_done_695_ == 0)
{
lean_object* v_e_x27_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref_known(v___x_691_, 1);
v_e_x27_696_ = lean_ctor_get(v_a_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v_a_692_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_e_x27_696_);
lean_dec(v_a_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; 
lean_inc_ref(v_e_x27_696_);
v___x_700_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_690_, v_e_x27_696_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
if (lean_obj_tag(v_a_701_) == 0)
{
uint8_t v_done_702_; lean_object* v___x_704_; 
v_done_702_ = lean_ctor_get_uint8(v_a_701_, 0);
lean_dec_ref_known(v_a_701_, 0);
lean_inc_ref(v_e_x27_696_);
if (v_isShared_699_ == 0)
{
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_e_x27_696_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*1, v_done_702_);
v___y_631_ = v___y_677_;
v___y_632_ = v___y_673_;
v___y_633_ = v___y_670_;
v___y_634_ = v___y_669_;
v___y_635_ = v___y_674_;
v___y_636_ = v___y_676_;
v___y_637_ = v___y_675_;
v___y_638_ = v___y_671_;
v___y_639_ = v___y_672_;
v_a_640_ = v___x_704_;
v_e_x27_641_ = v_e_x27_696_;
v_done_642_ = v_done_702_;
goto v___jp_630_;
}
}
else
{
lean_object* v_e_x27_706_; uint8_t v_done_707_; 
lean_del_object(v___x_698_);
lean_dec_ref(v_e_x27_696_);
v_e_x27_706_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_e_x27_706_);
v_done_707_ = lean_ctor_get_uint8(v_a_701_, sizeof(void*)*1);
v___y_631_ = v___y_677_;
v___y_632_ = v___y_673_;
v___y_633_ = v___y_670_;
v___y_634_ = v___y_669_;
v___y_635_ = v___y_674_;
v___y_636_ = v___y_676_;
v___y_637_ = v___y_675_;
v___y_638_ = v___y_671_;
v___y_639_ = v___y_672_;
v_a_640_ = v_a_701_;
v_e_x27_641_ = v_e_x27_706_;
v_done_642_ = v_done_707_;
goto v___jp_630_;
}
}
else
{
lean_del_object(v___x_698_);
lean_dec_ref(v_e_x27_696_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v_e_u2081_588_);
return v___x_700_;
}
}
}
else
{
lean_dec_ref_known(v_a_692_, 1);
v___y_644_ = v___y_669_;
v___y_645_ = v___y_670_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_677_;
v___y_648_ = v___y_674_;
v___y_649_ = v___y_676_;
v___y_650_ = v___y_675_;
v___y_651_ = v___y_671_;
v___y_652_ = v___y_672_;
v___y_653_ = v___x_691_;
goto v___jp_643_;
}
}
}
else
{
v___y_644_ = v___y_669_;
v___y_645_ = v___y_670_;
v___y_646_ = v___y_673_;
v___y_647_ = v___y_677_;
v___y_648_ = v___y_674_;
v___y_649_ = v___y_676_;
v___y_650_ = v___y_675_;
v___y_651_ = v___y_671_;
v___y_652_ = v___y_672_;
v___y_653_ = v___x_691_;
goto v___jp_643_;
}
}
else
{
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
v_r_600_ = v_a_688_;
v___y_601_ = v___y_671_;
goto v___jp_599_;
}
}
else
{
uint8_t v_done_709_; 
v_done_709_ = lean_ctor_get_uint8(v_a_688_, sizeof(void*)*1);
if (v_done_709_ == 0)
{
lean_object* v_e_x27_710_; 
v_e_x27_710_ = lean_ctor_get(v_a_688_, 0);
lean_inc_ref(v_e_x27_710_);
lean_dec_ref_known(v_a_688_, 1);
v_e_u2082_616_ = v_e_x27_710_;
v___y_617_ = v___y_669_;
v___y_618_ = v___y_670_;
v___y_619_ = v___y_671_;
v___y_620_ = v___y_672_;
v___y_621_ = v___y_673_;
v___y_622_ = v___y_674_;
v___y_623_ = v___y_675_;
v___y_624_ = v___y_676_;
v___y_625_ = v___y_677_;
goto v___jp_615_;
}
else
{
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
v_r_600_ = v_a_688_;
v___y_601_ = v___y_671_;
goto v___jp_599_;
}
}
}
else
{
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v_e_u2081_588_);
return v___x_687_;
}
}
}
}
v___jp_714_:
{
lean_object* v___x_726_; lean_object* v_cache_727_; lean_object* v___x_728_; 
v___x_726_ = lean_st_ref_get(v___y_719_);
v_cache_727_ = lean_ctor_get(v___x_726_, 1);
lean_inc_ref(v_cache_727_);
lean_dec(v___x_726_);
v___x_728_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_cache_727_, v_e_u2081_588_);
lean_dec_ref(v_cache_727_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v_e_u2081_588_);
v_val_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_val_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
lean_dec(v___x_728_);
v___x_737_ = lean_nat_add(v___y_716_, v___y_715_);
lean_dec(v___y_716_);
v___x_738_ = lean_unsigned_to_nat(1000u);
v___x_739_ = lean_nat_mod(v___x_737_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_nat_dec_eq(v___x_739_, v___x_740_);
lean_dec(v___x_739_);
if (v___x_741_ == 0)
{
v___y_668_ = v___x_737_;
v___y_669_ = v___y_717_;
v___y_670_ = v___y_718_;
v___y_671_ = v___y_719_;
v___y_672_ = v___y_720_;
v___y_673_ = v___y_721_;
v___y_674_ = v___y_722_;
v___y_675_ = v___y_723_;
v___y_676_ = v___y_724_;
v___y_677_ = v___y_725_;
goto v___jp_667_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0));
v___x_743_ = l_Lean_Core_checkSystem(v___x_742_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref_known(v___x_743_, 1);
v___y_668_ = v___x_737_;
v___y_669_ = v___y_717_;
v___y_670_ = v___y_718_;
v___y_671_ = v___y_719_;
v___y_672_ = v___y_720_;
v___y_673_ = v___y_721_;
v___y_674_ = v___y_722_;
v___y_675_ = v___y_723_;
v___y_676_ = v___y_724_;
v___y_677_ = v___y_725_;
goto v___jp_667_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v___x_737_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v_e_u2081_588_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_currRecDepth_658_, v___x_753_);
lean_dec(v_currRecDepth_658_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___x_754_);
v___x_756_ = v___x_664_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_toCold_657_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_ref_659_);
lean_ctor_set_uint16(v_reuseFailAlloc_771_, sizeof(void*)*3, v_optionFlags_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*3 + 2, v_suppressElabErrors_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*3 + 3, v_isRecordingDeps_662_);
v___x_756_ = v_reuseFailAlloc_771_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_numSteps_758_; lean_object* v_maxSteps_759_; uint8_t v___x_760_; 
v___x_757_ = lean_st_ref_get(v_a_591_);
v_numSteps_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_numSteps_758_);
lean_dec(v___x_757_);
v_maxSteps_759_ = lean_ctor_get(v_a_590_, 0);
v___x_760_ = lean_nat_dec_le(v_maxSteps_759_, v_numSteps_758_);
if (v___x_760_ == 0)
{
v___y_715_ = v___x_753_;
v___y_716_ = v_numSteps_758_;
v___y_717_ = v_a_589_;
v___y_718_ = v_a_590_;
v___y_719_ = v_a_591_;
v___y_720_ = v_a_592_;
v___y_721_ = v_a_593_;
v___y_722_ = v_a_594_;
v___y_723_ = v_a_595_;
v___y_724_ = v___x_756_;
v___y_725_ = v_a_597_;
goto v___jp_714_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_numSteps_758_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_e_u2081_588_);
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
v___x_762_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_761_, v_a_594_, v_a_595_, v___x_756_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v___x_756_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void lean_sym_dsimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_588_ = stack[0].m_obj;
lean_object* v_a_589_ = stack[1].m_obj;
lean_object* v_a_590_ = stack[2].m_obj;
lean_object* v_a_591_ = stack[3].m_obj;
lean_object* v_a_592_ = stack[4].m_obj;
lean_object* v_a_593_ = stack[5].m_obj;
lean_object* v_a_594_ = stack[6].m_obj;
lean_object* v_a_595_ = stack[7].m_obj;
lean_object* v_a_596_ = stack[8].m_obj;
lean_object* v_a_597_ = stack[9].m_obj;
lean_object* v_res_777_;
v_res_777_ = lean_sym_dsimp(v_e_u2081_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object* v_e_u2081_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = lean_sym_dsimp(v_e_u2081_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_799_, v_x_800_, v_x_801_);
lean_dec_ref(v_x_801_);
lean_dec_ref(v_x_800_);
return v_res_802_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, size_t v_x_805_, size_t v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_804_, v_x_805_, v_x_806_, v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_804_ = stack[1].m_obj;
size_t v_x_805_ = stack[2].m_num;
size_t v_x_806_ = stack[3].m_num;
lean_object* v_x_807_ = stack[4].m_obj;
lean_object* v_x_808_ = stack[5].m_obj;
lean_object* v_res_810_;
v_res_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_box(0), v_x_804_, v_x_805_, v_x_806_, v_x_807_, v_x_808_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
size_t v_x_42789__boxed_817_; size_t v_x_42790__boxed_818_; lean_object* v_res_819_; 
v_x_42789__boxed_817_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_x_42790__boxed_818_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_811_, v_x_812_, v_x_42789__boxed_817_, v_x_42790__boxed_818_, v_x_815_, v_x_816_);
return v_res_819_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, size_t v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_821_, v_x_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_821_ = stack[1].m_obj;
size_t v_x_822_ = stack[2].m_num;
lean_object* v_x_823_ = stack[3].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_box(0), v_x_821_, v_x_822_, v_x_823_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
size_t v_x_42817__boxed_830_; lean_object* v_res_831_; 
v_x_42817__boxed_830_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_res_831_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_826_, v_x_827_, v_x_42817__boxed_830_, v_x_829_);
lean_dec_ref(v_x_829_);
lean_dec_ref(v_x_827_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_832_, lean_object* v_n_833_, lean_object* v_k_834_, lean_object* v_v_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_833_, v_k_834_, v_v_835_);
return v___x_836_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_837_, size_t v_depth_838_, lean_object* v_keys_839_, lean_object* v_vals_840_, lean_object* v_heq_841_, lean_object* v_i_842_, lean_object* v_entries_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_838_, v_keys_839_, v_vals_840_, v_i_842_, v_entries_843_);
return v___x_844_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_838_ = stack[1].m_num;
lean_object* v_keys_839_ = stack[2].m_obj;
lean_object* v_vals_840_ = stack[3].m_obj;
lean_object* v_i_842_ = stack[5].m_obj;
lean_object* v_entries_843_ = stack[6].m_obj;
lean_object* v_res_845_;
v_res_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_box(0), v_depth_838_, v_keys_839_, v_vals_840_, lean_box(0), v_i_842_, v_entries_843_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_846_, lean_object* v_depth_847_, lean_object* v_keys_848_, lean_object* v_vals_849_, lean_object* v_heq_850_, lean_object* v_i_851_, lean_object* v_entries_852_){
_start:
{
size_t v_depth_boxed_853_; lean_object* v_res_854_; 
v_depth_boxed_853_ = lean_unbox_usize(v_depth_847_);
lean_dec(v_depth_847_);
v_res_854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_846_, v_depth_boxed_853_, v_keys_848_, v_vals_849_, v_heq_850_, v_i_851_, v_entries_852_);
lean_dec_ref(v_vals_849_);
lean_dec_ref(v_keys_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_855_, lean_object* v_keys_856_, lean_object* v_vals_857_, lean_object* v_heq_858_, lean_object* v_i_859_, lean_object* v_k_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_856_, v_vals_857_, v_i_859_, v_k_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_862_, lean_object* v_keys_863_, lean_object* v_vals_864_, lean_object* v_heq_865_, lean_object* v_i_866_, lean_object* v_k_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_862_, v_keys_863_, v_vals_864_, v_heq_865_, v_i_866_, v_k_867_);
lean_dec_ref(v_k_867_);
lean_dec_ref(v_vals_864_);
lean_dec_ref(v_keys_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_870_, v_x_871_, v_x_872_, v_x_873_);
return v___x_874_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
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
