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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
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
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*11);
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
lean_object* v___x_67_; lean_object* v_env_68_; lean_object* v___x_69_; lean_object* v_toCold_70_; lean_object* v_mctx_71_; lean_object* v_lctx_72_; lean_object* v_options_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = lean_st_ref_get(v___y_63_);
v_toCold_70_ = lean_ctor_get(v___y_64_, 0);
v_mctx_71_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_mctx_71_);
lean_dec(v___x_69_);
v_lctx_72_ = lean_ctor_get(v___y_62_, 2);
v_options_73_ = lean_ctor_get(v_toCold_70_, 2);
lean_inc_ref(v_options_73_);
lean_inc_ref(v_lctx_72_);
v___x_74_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_74_, 0, v_env_68_);
lean_ctor_set(v___x_74_, 1, v_mctx_71_);
lean_ctor_set(v___x_74_, 2, v_lctx_72_);
lean_ctor_set(v___x_74_, 3, v_options_73_);
v___x_75_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v_msgData_61_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1___boxed(lean_object* v_msgData_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msgData_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_ref_90_; lean_object* v___x_91_; lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_ref_90_ = lean_ctor_get(v___y_87_, 2);
v___x_91_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1_spec__1(v_msg_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_inc(v_ref_90_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_ref_90_);
lean_ctor_set(v___x_96_, 1, v_a_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 1);
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg___boxed(lean_object* v_msg_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__1));
v___x_112_ = l_Lean_stringToMessageData(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__3));
v___x_115_ = l_Lean_stringToMessageData(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(lean_object* v_e_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_a_128_; 
switch(lean_obj_tag(v_e_116_))
{
case 5:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_132_;
}
case 6:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_133_;
}
case 7:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_134_;
}
case 8:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_135_;
}
case 10:
{
lean_object* v_data_136_; lean_object* v_expr_137_; lean_object* v___x_138_; 
v_data_136_ = lean_ctor_get(v_e_116_, 0);
v_expr_137_ = lean_ctor_get(v_e_116_, 1);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_expr_137_);
v___x_138_ = lean_sym_dsimp(v_expr_137_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_161_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_161_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_161_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec_ref_known(v_a_139_, 0);
lean_dec_ref_known(v_e_116_, 2);
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v_e_x27_147_; size_t v___x_148_; size_t v___x_149_; uint8_t v___x_150_; 
lean_del_object(v___x_141_);
v_e_x27_147_ = lean_ctor_get(v_a_139_, 0);
lean_inc_ref(v_e_x27_147_);
lean_dec_ref_known(v_a_139_, 1);
v___x_148_ = lean_ptr_addr(v_expr_137_);
v___x_149_ = lean_ptr_addr(v_e_x27_147_);
v___x_150_ = lean_usize_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_inc(v_data_136_);
lean_dec_ref_known(v_e_116_, 2);
v___x_151_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__0___redArg(v_data_136_, v_e_x27_147_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_a_128_ = v_a_152_;
goto v___jp_127_;
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_153_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_151_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_151_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_147_);
v_a_128_ = v_e_116_;
goto v___jp_127_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_116_, 2);
return v___x_138_;
}
}
case 11:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__2);
v___x_163_ = l_Lean_indentExpr(v_e_116_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__4);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_166_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_167_;
}
default: 
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v_e_116_);
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___closed__0));
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
v___jp_127_:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = 0;
v___x_130_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_130_, 0, v_a_128_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep___boxed(lean_object* v_e_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(lean_object* v_00_u03b1_182_, lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v_msg_183_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___boxed(lean_object* v_00_u03b1_195_, lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1(v_00_u03b1_195_, v_msg_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(lean_object* v_e_210_, lean_object* v_r_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_numSteps_215_; lean_object* v_cache_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
v___x_214_ = lean_st_ref_take(v_a_212_);
v_numSteps_215_ = lean_ctor_get(v___x_214_, 0);
v_cache_216_ = lean_ctor_get(v___x_214_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v___x_214_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_cache_216_);
lean_inc(v_numSteps_215_);
lean_dec(v___x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___f_220_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_221_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_211_);
v___x_222_ = l_Lean_PersistentHashMap_insert___redArg(v___f_220_, v___f_221_, v_cache_216_, v_e_210_, v_r_211_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_222_);
v___x_224_ = v___x_218_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_numSteps_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_227_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_st_ref_put(v_a_212_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_r_211_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___boxed(lean_object* v_e_229_, lean_object* v_r_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg(v_e_229_, v_r_230_, v_a_231_);
lean_dec(v_a_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(lean_object* v_e_234_, lean_object* v_r_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_numSteps_247_; lean_object* v_cache_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v___x_246_ = lean_st_ref_take(v_a_238_);
v_numSteps_247_ = lean_ctor_get(v___x_246_, 0);
v_cache_248_ = lean_ctor_get(v___x_246_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v___x_246_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_cache_248_);
lean_inc(v_numSteps_247_);
lean_dec(v___x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___f_252_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__0));
v___f_253_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___redArg___closed__1));
lean_inc_ref(v_r_235_);
v___x_254_ = l_Lean_PersistentHashMap_insert___redArg(v___f_252_, v___f_253_, v_cache_248_, v_e_234_, v_r_235_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_numSteps_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_259_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_st_ref_put(v_a_238_, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_r_235_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult___boxed(lean_object* v_e_261_, lean_object* v_r_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_cacheResult(v_e_261_, v_r_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
return v_res_273_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = l_Lean_maxRecDepthErrorMessage;
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__3);
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__4);
v___x_284_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__2));
v___x_285_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(lean_object* v_ref_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___closed__5);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_ref_286_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg___boxed(lean_object* v_ref_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(lean_object* v_00_u03b1_294_, lean_object* v_ref_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_295_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___boxed(lean_object* v_00_u03b1_307_, lean_object* v_ref_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2(v_00_u03b1_307_, v_ref_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(lean_object* v_x_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_post_332_; lean_object* v___x_333_; 
v_post_332_ = lean_ctor_get(v___y_322_, 1);
lean_inc_ref(v_post_332_);
lean_inc(v___y_330_);
lean_inc_ref(v___y_329_);
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
lean_inc(v___y_322_);
v___x_333_ = lean_apply_11(v_post_332_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, lean_box(0));
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0___boxed(lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v_x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_378_; 
v_ks_351_ = lean_ctor_get(v_x_347_, 0);
v_vs_352_ = lean_ctor_get(v_x_347_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_347_);
if (v_isSharedCheck_378_ == 0)
{
v___x_354_ = v_x_347_;
v_isShared_355_ = v_isSharedCheck_378_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_vs_352_);
lean_inc(v_ks_351_);
lean_dec(v_x_347_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_378_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_ks_351_);
v___x_357_ = lean_nat_dec_lt(v_x_348_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_x_348_);
v___x_358_ = lean_array_push(v_ks_351_, v_x_349_);
v___x_359_ = lean_array_push(v_vs_352_, v_x_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_359_);
lean_ctor_set(v___x_354_, 0, v___x_358_);
v___x_361_ = v___x_354_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v_k_x27_363_; size_t v___x_364_; size_t v___x_365_; uint8_t v___x_366_; 
v_k_x27_363_ = lean_array_fget_borrowed(v_ks_351_, v_x_348_);
v___x_364_ = lean_ptr_addr(v_x_349_);
v___x_365_ = lean_ptr_addr(v_k_x27_363_);
v___x_366_ = lean_usize_dec_eq(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_368_; 
if (v_isShared_355_ == 0)
{
v___x_368_ = v___x_354_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_ks_351_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_vs_352_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_x_348_, v___x_369_);
lean_dec(v_x_348_);
v_x_347_ = v___x_368_;
v_x_348_ = v___x_370_;
goto _start;
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_array_fset(v_ks_351_, v_x_348_, v_x_349_);
v___x_374_ = lean_array_fset(v_vs_352_, v_x_348_, v_x_350_);
lean_dec(v_x_348_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_374_);
lean_ctor_set(v___x_354_, 0, v___x_373_);
v___x_376_ = v___x_354_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_n_379_, lean_object* v_k_380_, lean_object* v_v_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_n_379_, v___x_382_, v_k_380_, v_v_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(lean_object* v_x_385_, size_t v_x_386_, size_t v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v_es_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v_j_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_es_390_ = lean_ctor_get(v_x_385_, 0);
v___x_391_ = ((size_t)31ULL);
v___x_392_ = lean_usize_land(v_x_386_, v___x_391_);
v_j_393_ = lean_usize_to_nat(v___x_392_);
v___x_394_ = lean_array_get_size(v_es_390_);
v___x_395_ = lean_nat_dec_lt(v_j_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v_j_393_);
lean_dec(v_x_389_);
lean_dec_ref(v_x_388_);
return v_x_385_;
}
else
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_436_; 
lean_inc_ref(v_es_390_);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_385_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_x_385_, 0);
lean_dec(v_unused_437_);
v___x_397_ = v_x_385_;
v_isShared_398_ = v_isSharedCheck_436_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_x_385_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_436_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_v_399_; lean_object* v___x_400_; lean_object* v_xs_x27_401_; lean_object* v___y_403_; 
v_v_399_ = lean_array_fget(v_es_390_, v_j_393_);
v___x_400_ = lean_box(0);
v_xs_x27_401_ = lean_array_fset(v_es_390_, v_j_393_, v___x_400_);
switch(lean_obj_tag(v_v_399_))
{
case 0:
{
lean_object* v_key_408_; lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v_key_408_ = lean_ctor_get(v_v_399_, 0);
v_val_409_ = lean_ctor_get(v_v_399_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_v_399_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v_v_399_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_inc(v_key_408_);
lean_dec(v_v_399_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
size_t v___x_413_; size_t v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_ptr_addr(v_x_388_);
v___x_414_ = lean_ptr_addr(v_key_408_);
v___x_415_ = lean_usize_dec_eq(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_del_object(v___x_411_);
v___x_416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_408_, v_val_409_, v_x_388_, v_x_389_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___y_403_ = v___x_417_;
goto v___jp_402_;
}
else
{
lean_object* v___x_419_; 
lean_dec(v_val_409_);
lean_dec(v_key_408_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_x_389_);
lean_ctor_set(v___x_411_, 0, v_x_388_);
v___x_419_ = v___x_411_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_x_388_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_x_389_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v___y_403_ = v___x_419_;
goto v___jp_402_;
}
}
}
}
case 1:
{
lean_object* v_node_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_434_; 
v_node_422_ = lean_ctor_get(v_v_399_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_v_399_);
if (v_isSharedCheck_434_ == 0)
{
v___x_424_ = v_v_399_;
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_node_422_);
lean_dec(v_v_399_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_426_ = ((size_t)5ULL);
v___x_427_ = lean_usize_shift_right(v_x_386_, v___x_426_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_x_387_, v___x_428_);
v___x_430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_node_422_, v___x_427_, v___x_429_, v_x_388_, v_x_389_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_430_);
v___x_432_ = v___x_424_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v___y_403_ = v___x_432_;
goto v___jp_402_;
}
}
}
default: 
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_x_388_);
lean_ctor_set(v___x_435_, 1, v_x_389_);
v___y_403_ = v___x_435_;
goto v___jp_402_;
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_array_fset(v_xs_x27_401_, v_j_393_, v___y_403_);
lean_dec(v_j_393_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_404_);
v___x_406_ = v___x_397_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_ks_438_; lean_object* v_vs_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_457_; 
v_ks_438_ = lean_ctor_get(v_x_385_, 0);
v_vs_439_ = lean_ctor_get(v_x_385_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_385_);
if (v_isSharedCheck_457_ == 0)
{
v___x_441_ = v_x_385_;
v_isShared_442_ = v_isSharedCheck_457_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_vs_439_);
lean_inc(v_ks_438_);
lean_dec(v_x_385_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_457_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_ks_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_vs_439_);
v___x_444_ = v_reuseFailAlloc_456_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v_newNode_445_; size_t v___x_446_; uint8_t v___x_447_; 
v_newNode_445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v___x_444_, v_x_388_, v_x_389_);
v___x_446_ = ((size_t)7ULL);
v___x_447_ = lean_usize_dec_le(v___x_446_, v_x_387_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_445_);
v___x_449_ = lean_unsigned_to_nat(4u);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v_ks_451_; lean_object* v_vs_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_ks_451_ = lean_ctor_get(v_newNode_445_, 0);
lean_inc_ref(v_ks_451_);
v_vs_452_ = lean_ctor_get(v_newNode_445_, 1);
lean_inc_ref(v_vs_452_);
lean_dec_ref(v_newNode_445_);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___closed__0);
v___x_455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_x_387_, v_ks_451_, v_vs_452_, v___x_453_, v___x_454_);
lean_dec_ref(v_vs_452_);
lean_dec_ref(v_ks_451_);
return v___x_455_;
}
else
{
return v_newNode_445_;
}
}
else
{
return v_newNode_445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(size_t v_depth_458_, lean_object* v_keys_459_, lean_object* v_vals_460_, lean_object* v_i_461_, lean_object* v_entries_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_array_get_size(v_keys_459_);
v___x_464_ = lean_nat_dec_lt(v_i_461_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec(v_i_461_);
return v_entries_462_;
}
else
{
lean_object* v_k_465_; lean_object* v_v_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; uint64_t v___x_470_; size_t v_h_471_; size_t v___x_472_; lean_object* v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v_h_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_k_465_ = lean_array_fget_borrowed(v_keys_459_, v_i_461_);
v_v_466_ = lean_array_fget_borrowed(v_vals_460_, v_i_461_);
v___x_467_ = lean_ptr_addr(v_k_465_);
v___x_468_ = ((size_t)3ULL);
v___x_469_ = lean_usize_shift_right(v___x_467_, v___x_468_);
v___x_470_ = lean_usize_to_uint64(v___x_469_);
v_h_471_ = lean_uint64_to_usize(v___x_470_);
v___x_472_ = ((size_t)5ULL);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_sub(v_depth_458_, v___x_474_);
v___x_476_ = lean_usize_mul(v___x_472_, v___x_475_);
v_h_477_ = lean_usize_shift_right(v_h_471_, v___x_476_);
v___x_478_ = lean_nat_add(v_i_461_, v___x_473_);
lean_dec(v_i_461_);
lean_inc(v_v_466_);
lean_inc(v_k_465_);
v___x_479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_entries_462_, v_h_477_, v_depth_458_, v_k_465_, v_v_466_);
v_i_461_ = v___x_478_;
v_entries_462_ = v___x_479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_481_, lean_object* v_keys_482_, lean_object* v_vals_483_, lean_object* v_i_484_, lean_object* v_entries_485_){
_start:
{
size_t v_depth_boxed_486_; lean_object* v_res_487_; 
v_depth_boxed_486_ = lean_unbox_usize(v_depth_481_);
lean_dec(v_depth_481_);
v_res_487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_boxed_486_, v_keys_482_, v_vals_483_, v_i_484_, v_entries_485_);
lean_dec_ref(v_vals_483_);
lean_dec_ref(v_keys_482_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
size_t v_x_41668__boxed_493_; size_t v_x_41669__boxed_494_; lean_object* v_res_495_; 
v_x_41668__boxed_493_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_x_41669__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_res_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_488_, v_x_41668__boxed_493_, v_x_41669__boxed_494_, v_x_491_, v_x_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; uint64_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_499_ = lean_ptr_addr(v_x_497_);
v___x_500_ = ((size_t)3ULL);
v___x_501_ = lean_usize_shift_right(v___x_499_, v___x_500_);
v___x_502_ = lean_usize_to_uint64(v___x_501_);
v___x_503_ = lean_uint64_to_usize(v___x_502_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_496_, v___x_503_, v___x_504_, v_x_497_, v_x_498_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_506_, lean_object* v_vals_507_, lean_object* v_i_508_, lean_object* v_k_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_array_get_size(v_keys_506_);
v___x_511_ = lean_nat_dec_lt(v_i_508_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec(v_i_508_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
else
{
lean_object* v_k_x27_513_; size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v_k_x27_513_ = lean_array_fget_borrowed(v_keys_506_, v_i_508_);
v___x_514_ = lean_ptr_addr(v_k_509_);
v___x_515_ = lean_ptr_addr(v_k_x27_513_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_i_508_, v___x_517_);
lean_dec(v_i_508_);
v_i_508_ = v___x_518_;
goto _start;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_array_fget_borrowed(v_vals_507_, v_i_508_);
lean_dec(v_i_508_);
lean_inc(v___x_520_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_522_, lean_object* v_vals_523_, lean_object* v_i_524_, lean_object* v_k_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_522_, v_vals_523_, v_i_524_, v_k_525_);
lean_dec_ref(v_k_525_);
lean_dec_ref(v_vals_523_);
lean_dec_ref(v_keys_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(lean_object* v_x_527_, size_t v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_es_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v_j_534_; lean_object* v___x_535_; 
v_es_530_ = lean_ctor_get(v_x_527_, 0);
v___x_531_ = lean_box(2);
v___x_532_ = ((size_t)31ULL);
v___x_533_ = lean_usize_land(v_x_528_, v___x_532_);
v_j_534_ = lean_usize_to_nat(v___x_533_);
v___x_535_ = lean_array_get_borrowed(v___x_531_, v_es_530_, v_j_534_);
lean_dec(v_j_534_);
switch(lean_obj_tag(v___x_535_))
{
case 0:
{
lean_object* v_key_536_; lean_object* v_val_537_; size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v_key_536_ = lean_ctor_get(v___x_535_, 0);
v_val_537_ = lean_ctor_get(v___x_535_, 1);
v___x_538_ = lean_ptr_addr(v_x_529_);
v___x_539_ = lean_ptr_addr(v_key_536_);
v___x_540_ = lean_usize_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_box(0);
return v___x_541_;
}
else
{
lean_object* v___x_542_; 
lean_inc(v_val_537_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_val_537_);
return v___x_542_;
}
}
case 1:
{
lean_object* v_node_543_; size_t v___x_544_; size_t v___x_545_; 
v_node_543_ = lean_ctor_get(v___x_535_, 0);
v___x_544_ = ((size_t)5ULL);
v___x_545_ = lean_usize_shift_right(v_x_528_, v___x_544_);
v_x_527_ = v_node_543_;
v_x_528_ = v___x_545_;
goto _start;
}
default: 
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
}
}
else
{
lean_object* v_ks_548_; lean_object* v_vs_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_ks_548_ = lean_ctor_get(v_x_527_, 0);
v_vs_549_ = lean_ctor_get(v_x_527_, 1);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_ks_548_, v_vs_549_, v___x_550_, v_x_529_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
size_t v_x_41869__boxed_555_; lean_object* v_res_556_; 
v_x_41869__boxed_555_ = lean_unbox_usize(v_x_553_);
lean_dec(v_x_553_);
v_res_556_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_552_, v_x_41869__boxed_555_, v_x_554_);
lean_dec_ref(v_x_554_);
lean_dec_ref(v_x_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; uint64_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
v___x_559_ = lean_ptr_addr(v_x_558_);
v___x_560_ = ((size_t)3ULL);
v___x_561_ = lean_usize_shift_right(v___x_559_, v___x_560_);
v___x_562_ = lean_usize_to_uint64(v___x_561_);
v___x_563_ = lean_uint64_to_usize(v___x_562_);
v___x_564_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_557_, v___x_563_, v_x_558_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg___boxed(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_565_, v_x_566_);
lean_dec_ref(v_x_566_);
lean_dec_ref(v_x_565_);
return v_res_567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__1));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* lean_sym_dsimp(lean_object* v_e_u2081_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_r_584_; lean_object* v___y_585_; lean_object* v_e_u2082_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v_a_624_; lean_object* v_e_x27_625_; uint8_t v_done_626_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v_toCold_641_; lean_object* v_currRecDepth_642_; lean_object* v_ref_643_; uint8_t v_diag_644_; uint8_t v_suppressElabErrors_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_759_; 
v_toCold_641_ = lean_ctor_get(v_a_580_, 0);
v_currRecDepth_642_ = lean_ctor_get(v_a_580_, 1);
v_ref_643_ = lean_ctor_get(v_a_580_, 2);
v_diag_644_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*3);
v_suppressElabErrors_645_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*3 + 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_580_);
if (v_isSharedCheck_759_ == 0)
{
v___x_647_ = v_a_580_;
v_isShared_648_ = v_isSharedCheck_759_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_ref_643_);
lean_inc(v_currRecDepth_642_);
lean_inc(v_toCold_641_);
lean_dec(v_a_580_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_759_;
goto v_resetjp_646_;
}
v___jp_583_:
{
lean_object* v___x_586_; lean_object* v_numSteps_587_; lean_object* v_cache_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_598_; 
v___x_586_ = lean_st_ref_take(v___y_585_);
v_numSteps_587_ = lean_ctor_get(v___x_586_, 0);
v_cache_588_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_598_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_cache_588_);
lean_inc(v_numSteps_587_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_inc_ref(v_r_584_);
v___x_592_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_cache_588_, v_e_u2081_572_, v_r_584_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_numSteps_587_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_592_);
v___x_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_st_ref_put(v___y_585_, v___x_594_);
lean_dec(v___y_585_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_r_584_);
return v___x_596_;
}
}
}
v___jp_599_:
{
lean_object* v___x_610_; 
lean_inc(v___y_603_);
lean_inc_ref(v_e_u2082_600_);
v___x_610_ = lean_sym_dsimp(v_e_u2082_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
if (lean_obj_tag(v_a_611_) == 0)
{
uint8_t v_done_612_; lean_object* v___x_613_; 
v_done_612_ = lean_ctor_get_uint8(v_a_611_, 0);
lean_dec_ref_known(v_a_611_, 0);
v___x_613_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_613_, 0, v_e_u2082_600_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*1, v_done_612_);
v_r_584_ = v___x_613_;
v___y_585_ = v___y_603_;
goto v___jp_583_;
}
else
{
lean_dec_ref(v_e_u2082_600_);
v_r_584_ = v_a_611_;
v___y_585_ = v___y_603_;
goto v___jp_583_;
}
}
else
{
lean_dec(v___y_603_);
lean_dec_ref(v_e_u2082_600_);
lean_dec_ref(v_e_u2081_572_);
return v___x_610_;
}
}
v___jp_614_:
{
if (v_done_626_ == 0)
{
lean_dec_ref(v_a_624_);
v_e_u2082_600_ = v_e_x27_625_;
v___y_601_ = v___y_616_;
v___y_602_ = v___y_619_;
v___y_603_ = v___y_618_;
v___y_604_ = v___y_621_;
v___y_605_ = v___y_620_;
v___y_606_ = v___y_615_;
v___y_607_ = v___y_623_;
v___y_608_ = v___y_617_;
v___y_609_ = v___y_622_;
goto v___jp_599_;
}
else
{
lean_dec_ref(v_e_x27_625_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
v_r_584_ = v_a_624_;
v___y_585_ = v___y_618_;
goto v___jp_583_;
}
}
v___jp_627_:
{
if (lean_obj_tag(v___y_637_) == 0)
{
lean_object* v_a_638_; 
v_a_638_ = lean_ctor_get(v___y_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___y_637_, 1);
if (lean_obj_tag(v_a_638_) == 0)
{
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
v_r_584_ = v_a_638_;
v___y_585_ = v___y_631_;
goto v___jp_583_;
}
else
{
lean_object* v_e_x27_639_; uint8_t v_done_640_; 
v_e_x27_639_ = lean_ctor_get(v_a_638_, 0);
lean_inc_ref(v_e_x27_639_);
v_done_640_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*1);
v___y_615_ = v___y_629_;
v___y_616_ = v___y_628_;
v___y_617_ = v___y_630_;
v___y_618_ = v___y_631_;
v___y_619_ = v___y_632_;
v___y_620_ = v___y_633_;
v___y_621_ = v___y_634_;
v___y_622_ = v___y_636_;
v___y_623_ = v___y_635_;
v_a_624_ = v_a_638_;
v_e_x27_625_ = v_e_x27_639_;
v_done_626_ = v_done_640_;
goto v___jp_614_;
}
}
else
{
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v_e_u2081_572_);
return v___y_637_;
}
}
v_resetjp_646_:
{
lean_object* v_maxRecDepth_649_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_maxRecDepth_649_ = lean_ctor_get(v_toCold_641_, 3);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_dec_eq(v_maxRecDepth_649_, v___x_755_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_eq(v_currRecDepth_642_, v_maxRecDepth_649_);
if (v___x_757_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v___x_758_; 
lean_del_object(v___x_647_);
lean_dec(v_currRecDepth_642_);
lean_dec_ref(v_toCold_641_);
lean_dec(v_a_581_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_e_u2081_572_);
v___x_758_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__2___redArg(v_ref_643_);
return v___x_758_;
}
}
else
{
goto v___jp_735_;
}
v___jp_650_:
{
lean_object* v___x_661_; lean_object* v_cache_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_695_; 
v___x_661_ = lean_st_ref_take(v___y_654_);
v_cache_662_ = lean_ctor_get(v___x_661_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_661_, 0);
lean_dec(v_unused_696_);
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_695_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_cache_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_695_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___y_651_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___y_651_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_cache_662_);
v___x_667_ = v_reuseFailAlloc_694_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v_pre_669_; lean_object* v___x_670_; 
v___x_668_ = lean_st_ref_put(v___y_654_, v___x_667_);
v_pre_669_ = lean_ctor_get(v___y_652_, 0);
lean_inc_ref(v_pre_669_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v_e_u2081_572_);
v___x_670_ = lean_apply_11(v_pre_669_, v_e_u2081_572_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, lean_box(0));
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
if (lean_obj_tag(v_a_671_) == 0)
{
uint8_t v_done_672_; 
v_done_672_ = lean_ctor_get_uint8(v_a_671_, 0);
if (v_done_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref_known(v_a_671_, 0);
lean_inc_ref(v_e_u2081_572_);
v___x_673_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep(v_e_u2081_572_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
v___x_675_ = lean_box(0);
if (lean_obj_tag(v_a_674_) == 0)
{
uint8_t v_done_676_; 
v_done_676_ = lean_ctor_get_uint8(v_a_674_, 0);
lean_dec_ref_known(v_a_674_, 0);
if (v_done_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref_known(v___x_673_, 1);
lean_inc_ref(v_e_u2081_572_);
v___x_677_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_675_, v_e_u2081_572_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
v___y_628_ = v___y_652_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_656_;
v___y_634_ = v___y_655_;
v___y_635_ = v___y_658_;
v___y_636_ = v___y_660_;
v___y_637_ = v___x_677_;
goto v___jp_627_;
}
else
{
v___y_628_ = v___y_652_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_656_;
v___y_634_ = v___y_655_;
v___y_635_ = v___y_658_;
v___y_636_ = v___y_660_;
v___y_637_ = v___x_673_;
goto v___jp_627_;
}
}
else
{
uint8_t v_done_678_; 
v_done_678_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*1);
if (v_done_678_ == 0)
{
lean_object* v_e_x27_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref_known(v___x_673_, 1);
v_e_x27_679_ = lean_ctor_get(v_a_674_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_691_ == 0)
{
v___x_681_ = v_a_674_;
v_isShared_682_ = v_isSharedCheck_691_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_e_x27_679_);
lean_dec(v_a_674_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_691_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; 
lean_inc_ref(v_e_x27_679_);
v___x_683_ = l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___lam__0(v___x_675_, v_e_x27_679_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
if (lean_obj_tag(v_a_684_) == 0)
{
uint8_t v_done_685_; lean_object* v___x_687_; 
v_done_685_ = lean_ctor_get_uint8(v_a_684_, 0);
lean_dec_ref_known(v_a_684_, 0);
lean_inc_ref(v_e_x27_679_);
if (v_isShared_682_ == 0)
{
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_e_x27_679_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*1, v_done_685_);
v___y_615_ = v___y_657_;
v___y_616_ = v___y_652_;
v___y_617_ = v___y_659_;
v___y_618_ = v___y_654_;
v___y_619_ = v___y_653_;
v___y_620_ = v___y_656_;
v___y_621_ = v___y_655_;
v___y_622_ = v___y_660_;
v___y_623_ = v___y_658_;
v_a_624_ = v___x_687_;
v_e_x27_625_ = v_e_x27_679_;
v_done_626_ = v_done_685_;
goto v___jp_614_;
}
}
else
{
lean_object* v_e_x27_689_; uint8_t v_done_690_; 
lean_del_object(v___x_681_);
lean_dec_ref(v_e_x27_679_);
v_e_x27_689_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_e_x27_689_);
v_done_690_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*1);
v___y_615_ = v___y_657_;
v___y_616_ = v___y_652_;
v___y_617_ = v___y_659_;
v___y_618_ = v___y_654_;
v___y_619_ = v___y_653_;
v___y_620_ = v___y_656_;
v___y_621_ = v___y_655_;
v___y_622_ = v___y_660_;
v___y_623_ = v___y_658_;
v_a_624_ = v_a_684_;
v_e_x27_625_ = v_e_x27_689_;
v_done_626_ = v_done_690_;
goto v___jp_614_;
}
}
else
{
lean_del_object(v___x_681_);
lean_dec_ref(v_e_x27_679_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v_e_u2081_572_);
return v___x_683_;
}
}
}
else
{
lean_dec_ref_known(v_a_674_, 1);
v___y_628_ = v___y_652_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_656_;
v___y_634_ = v___y_655_;
v___y_635_ = v___y_658_;
v___y_636_ = v___y_660_;
v___y_637_ = v___x_673_;
goto v___jp_627_;
}
}
}
else
{
v___y_628_ = v___y_652_;
v___y_629_ = v___y_657_;
v___y_630_ = v___y_659_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_656_;
v___y_634_ = v___y_655_;
v___y_635_ = v___y_658_;
v___y_636_ = v___y_660_;
v___y_637_ = v___x_673_;
goto v___jp_627_;
}
}
else
{
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
v_r_584_ = v_a_671_;
v___y_585_ = v___y_654_;
goto v___jp_583_;
}
}
else
{
uint8_t v_done_692_; 
v_done_692_ = lean_ctor_get_uint8(v_a_671_, sizeof(void*)*1);
if (v_done_692_ == 0)
{
lean_object* v_e_x27_693_; 
v_e_x27_693_ = lean_ctor_get(v_a_671_, 0);
lean_inc_ref(v_e_x27_693_);
lean_dec_ref_known(v_a_671_, 1);
v_e_u2082_600_ = v_e_x27_693_;
v___y_601_ = v___y_652_;
v___y_602_ = v___y_653_;
v___y_603_ = v___y_654_;
v___y_604_ = v___y_655_;
v___y_605_ = v___y_656_;
v___y_606_ = v___y_657_;
v___y_607_ = v___y_658_;
v___y_608_ = v___y_659_;
v___y_609_ = v___y_660_;
goto v___jp_599_;
}
else
{
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
v_r_584_ = v_a_671_;
v___y_585_ = v___y_654_;
goto v___jp_583_;
}
}
}
else
{
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v_e_u2081_572_);
return v___x_670_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_709_; lean_object* v_cache_710_; lean_object* v___x_711_; 
v___x_709_ = lean_st_ref_get(v___y_702_);
v_cache_710_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_cache_710_);
lean_dec(v___x_709_);
v___x_711_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_cache_710_, v_e_u2081_572_);
lean_dec_ref(v_cache_710_);
if (lean_obj_tag(v___x_711_) == 1)
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_698_);
lean_dec_ref(v_e_u2081_572_);
v_val_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 0);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_val_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
lean_dec(v___x_711_);
v___x_720_ = lean_nat_add(v___y_698_, v___y_699_);
lean_dec(v___y_698_);
v___x_721_ = lean_unsigned_to_nat(1000u);
v___x_722_ = lean_nat_mod(v___x_720_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
v___y_651_ = v___x_720_;
v___y_652_ = v___y_700_;
v___y_653_ = v___y_701_;
v___y_654_ = v___y_702_;
v___y_655_ = v___y_703_;
v___y_656_ = v___y_704_;
v___y_657_ = v___y_705_;
v___y_658_ = v___y_706_;
v___y_659_ = v___y_707_;
v___y_660_ = v___y_708_;
goto v___jp_650_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__0));
v___x_726_ = l_Lean_Core_checkSystem(v___x_725_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_dec_ref_known(v___x_726_, 1);
v___y_651_ = v___x_720_;
v___y_652_ = v___y_700_;
v___y_653_ = v___y_701_;
v___y_654_ = v___y_702_;
v___y_655_ = v___y_703_;
v___y_656_ = v___y_704_;
v___y_657_ = v___y_705_;
v___y_658_ = v___y_706_;
v___y_659_ = v___y_707_;
v___y_660_ = v___y_708_;
goto v___jp_650_;
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v___x_720_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v_e_u2081_572_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
v___jp_735_:
{
lean_object* v___x_736_; lean_object* v_numSteps_737_; lean_object* v_maxSteps_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_736_ = lean_st_ref_get(v_a_575_);
v_numSteps_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_numSteps_737_);
lean_dec(v___x_736_);
v_maxSteps_738_ = lean_ctor_get(v_a_574_, 0);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_currRecDepth_642_, v___x_739_);
lean_dec(v_currRecDepth_642_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_740_);
v___x_742_ = v___x_647_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_toCold_641_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_ref_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3, v_diag_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3 + 1, v_suppressElabErrors_645_);
v___x_742_ = v_reuseFailAlloc_754_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
uint8_t v___x_743_; 
v___x_743_ = lean_nat_dec_le(v_maxSteps_738_, v_numSteps_737_);
if (v___x_743_ == 0)
{
v___y_698_ = v_numSteps_737_;
v___y_699_ = v___x_739_;
v___y_700_ = v_a_573_;
v___y_701_ = v_a_574_;
v___y_702_ = v_a_575_;
v___y_703_ = v_a_576_;
v___y_704_ = v_a_577_;
v___y_705_ = v_a_578_;
v___y_706_ = v_a_579_;
v___y_707_ = v___x_742_;
v___y_708_ = v_a_581_;
goto v___jp_697_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_numSteps_737_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_e_u2081_572_);
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2, &l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2_once, _init_l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___closed__2);
v___x_745_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpStep_spec__1___redArg(v___x_744_, v_a_578_, v_a_579_, v___x_742_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v___x_742_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl___boxed(lean_object* v_e_u2081_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = lean_sym_dsimp(v_e_u2081_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0___redArg(v_x_773_, v_x_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___redArg(v_x_778_, v_x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1___boxed(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1(v_00_u03b2_781_, v_x_782_, v_x_783_);
lean_dec_ref(v_x_783_);
lean_dec_ref(v_x_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(lean_object* v_00_u03b2_785_, lean_object* v_x_786_, size_t v_x_787_, size_t v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___redArg(v_x_786_, v_x_787_, v_x_788_, v_x_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_42303__boxed_798_; size_t v_x_42304__boxed_799_; lean_object* v_res_800_; 
v_x_42303__boxed_798_ = lean_unbox_usize(v_x_794_);
lean_dec(v_x_794_);
v_x_42304__boxed_799_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_res_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0(v_00_u03b2_792_, v_x_793_, v_x_42303__boxed_798_, v_x_42304__boxed_799_, v_x_796_, v_x_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, size_t v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___redArg(v_x_802_, v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_42320__boxed_810_; lean_object* v_res_811_; 
v_x_42320__boxed_810_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_res_811_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2(v_00_u03b2_806_, v_x_807_, v_x_42320__boxed_810_, v_x_809_);
lean_dec_ref(v_x_809_);
lean_dec_ref(v_x_807_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_812_, lean_object* v_n_813_, lean_object* v_k_814_, lean_object* v_v_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2___redArg(v_n_813_, v_k_814_, v_v_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_817_, size_t v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___redArg(v_depth_818_, v_keys_819_, v_vals_820_, v_i_822_, v_entries_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_825_, lean_object* v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_entries_831_){
_start:
{
size_t v_depth_boxed_832_; lean_object* v_res_833_; 
v_depth_boxed_832_ = lean_unbox_usize(v_depth_826_);
lean_dec(v_depth_826_);
v_res_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__3(v_00_u03b2_825_, v_depth_boxed_832_, v_keys_827_, v_vals_828_, v_heq_829_, v_i_830_, v_entries_831_);
lean_dec_ref(v_vals_828_);
lean_dec_ref(v_keys_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_k_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___redArg(v_keys_835_, v_vals_836_, v_i_838_, v_k_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_heq_844_, lean_object* v_i_845_, lean_object* v_k_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__1_spec__2_spec__6(v_00_u03b2_841_, v_keys_842_, v_vals_843_, v_heq_844_, v_i_845_, v_k_846_);
lean_dec_ref(v_k_846_);
lean_dec_ref(v_vals_843_);
lean_dec_ref(v_keys_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_DSimp_Main_0__Lean_Meta_Sym_DSimp_dsimpImpl_spec__0_spec__0_spec__2_spec__4___redArg(v_x_849_, v_x_850_, v_x_851_, v_x_852_);
return v___x_853_;
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
