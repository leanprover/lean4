// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Main
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Have import Lean.Meta.Sym.Simp.Lambda import Lean.Meta.Sym.Simp.Forall
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1;
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_16 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_16);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_mdata___override(x_1, x_2);
x_12 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected kernel projection term during simplification", 55, 55);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\npre-process and fold them as projection applications", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_Simp_simpAppArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 6:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
case 7:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Simp_simpForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
case 8:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_simpLet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
case 10:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_17 = lean_sym_simp(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_20 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0;
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
uint8_t x_21; 
lean_free_object(x_17);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(x_15, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = 0;
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_27);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
lean_ctor_set(x_19, 0, x_28);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_19);
lean_dec_ref(x_23);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(x_15, x_34, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = 0;
x_40 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_35);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
}
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_46 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0;
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
x_51 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__0___redArg(x_15, x_48, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = 0;
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(1, 2, 1);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_50);
lean_dec_ref(x_49);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_17;
}
}
case 11:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_64, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_65;
}
default: 
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0;
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
x_9 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
lean_inc_ref(x_2);
x_10 = l_Lean_PersistentHashMap_insert___redArg(x_8, x_9, x_7, x_1, x_2);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_17 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
x_18 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
lean_inc_ref(x_2);
x_19 = l_Lean_PersistentHashMap_insert___redArg(x_17, x_18, x_13, x_1, x_2);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
x_21 = lean_st_ref_set(x_3, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_take(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
x_16 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
lean_inc_ref(x_2);
x_17 = l_Lean_PersistentHashMap_insert___redArg(x_15, x_16, x_14, x_1, x_2);
lean_ctor_set(x_12, 0, x_17);
x_18 = lean_st_ref_set(x_5, x_12);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_12, 2);
x_23 = lean_ctor_get(x_12, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_24 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0;
x_25 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1;
lean_inc_ref(x_2);
x_26 = l_Lean_PersistentHashMap_insert___redArg(x_24, x_25, x_20, x_1, x_2);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
x_28 = lean_st_ref_set(x_5, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_2);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4;
x_2 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_12);
x_13 = lean_apply_10(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`simp` failed: maximum number of steps exceeded", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_sym_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_131; 
x_131 = !lean_is_exclusive(x_8);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_132 = lean_ctor_get(x_8, 0);
x_133 = lean_ctor_get(x_8, 1);
x_134 = lean_ctor_get(x_8, 2);
x_135 = lean_ctor_get(x_8, 3);
x_136 = lean_ctor_get(x_8, 4);
x_137 = lean_ctor_get(x_8, 5);
x_138 = lean_ctor_get(x_8, 6);
x_139 = lean_ctor_get(x_8, 7);
x_140 = lean_ctor_get(x_8, 8);
x_141 = lean_ctor_get(x_8, 9);
x_142 = lean_ctor_get(x_8, 10);
x_143 = lean_ctor_get(x_8, 11);
x_144 = lean_ctor_get(x_8, 12);
x_145 = lean_ctor_get(x_8, 13);
x_146 = lean_nat_dec_eq(x_135, x_136);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_st_ref_get(x_4);
x_148 = l_Lean_Meta_Sym_Simp_getConfig___redArg(x_3);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_376; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_147, 2);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
lean_dec(x_149);
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_nat_add(x_135, x_350);
lean_dec(x_135);
lean_ctor_set(x_8, 3, x_351);
x_376 = lean_nat_dec_le(x_152, x_151);
lean_dec(x_152);
if (x_376 == 0)
{
x_352 = x_2;
x_353 = x_3;
x_354 = x_4;
x_355 = x_5;
x_356 = x_6;
x_357 = x_7;
x_358 = x_9;
x_359 = lean_box(0);
goto block_375;
}
else
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_377 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
x_378 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_377, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_379 = !lean_is_exclusive(x_378);
if (x_379 == 0)
{
return x_378;
}
else
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_378, 0);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_380);
return x_381;
}
}
block_349:
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_st_ref_take(x_156);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_163, 2);
lean_dec(x_165);
lean_ctor_set(x_163, 2, x_153);
x_166 = lean_st_ref_set(x_156, x_163);
x_167 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_167);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_168 = lean_apply_10(x_167, x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, lean_box(0));
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_168, 0);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = lean_ctor_get_uint8(x_170, 0);
if (x_171 == 0)
{
lean_object* x_172; 
lean_free_object(x_168);
lean_dec_ref(x_170);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_172 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_box(0);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_173, 0);
lean_dec_ref(x_173);
if (x_175 == 0)
{
lean_object* x_176; 
lean_dec_ref(x_172);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_176 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_174, x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_176;
goto block_130;
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_172;
goto block_130;
}
}
else
{
uint8_t x_177; 
x_177 = lean_ctor_get_uint8(x_173, sizeof(void*)*2);
if (x_177 == 0)
{
uint8_t x_178; 
lean_dec_ref(x_172);
x_178 = !lean_is_exclusive(x_173);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_179);
x_181 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_174, x_179, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = lean_ctor_get_uint8(x_182, 0);
lean_dec_ref(x_182);
lean_inc_ref(x_180);
lean_inc_ref(x_179);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_183);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_173;
x_71 = x_179;
x_72 = x_180;
x_73 = x_183;
x_74 = lean_box(0);
goto block_89;
}
else
{
uint8_t x_184; 
lean_free_object(x_173);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_182, 0);
x_186 = lean_ctor_get(x_182, 1);
x_187 = lean_ctor_get_uint8(x_182, sizeof(void*)*2);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_185);
lean_inc_ref(x_1);
x_188 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_179, x_180, x_185, x_186, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc(x_189);
lean_inc_ref(x_185);
lean_ctor_set(x_182, 1, x_189);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_182;
x_71 = x_185;
x_72 = x_189;
x_73 = x_187;
x_74 = lean_box(0);
goto block_89;
}
else
{
uint8_t x_190; 
lean_free_object(x_182);
lean_dec_ref(x_185);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
x_190 = !lean_is_exclusive(x_188);
if (x_190 == 0)
{
return x_188;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_182, 0);
x_194 = lean_ctor_get(x_182, 1);
x_195 = lean_ctor_get_uint8(x_182, sizeof(void*)*2);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_182);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_193);
lean_inc_ref(x_1);
x_196 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_179, x_180, x_193, x_194, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
lean_inc(x_197);
lean_inc_ref(x_193);
x_198 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_195);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_198;
x_71 = x_193;
x_72 = x_197;
x_73 = x_195;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_193);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_200 = x_196;
} else {
 lean_dec_ref(x_196);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
}
}
else
{
lean_free_object(x_173);
lean_dec_ref(x_180);
lean_dec_ref(x_179);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_181;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_173, 0);
x_203 = lean_ctor_get(x_173, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_173);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_202);
x_204 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_174, x_202, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; lean_object* x_207; 
x_206 = lean_ctor_get_uint8(x_205, 0);
lean_dec_ref(x_205);
lean_inc_ref(x_203);
lean_inc_ref(x_202);
x_207 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set_uint8(x_207, sizeof(void*)*2, x_206);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_207;
x_71 = x_202;
x_72 = x_203;
x_73 = x_206;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_205, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc_ref(x_209);
x_210 = lean_ctor_get_uint8(x_205, sizeof(void*)*2);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_211 = x_205;
} else {
 lean_dec_ref(x_205);
 x_211 = lean_box(0);
}
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_208);
lean_inc_ref(x_1);
x_212 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_202, x_203, x_208, x_209, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
lean_inc(x_213);
lean_inc_ref(x_208);
if (lean_is_scalar(x_211)) {
 x_214 = lean_alloc_ctor(1, 2, 1);
} else {
 x_214 = x_211;
}
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_210);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_214;
x_71 = x_208;
x_72 = x_213;
x_73 = x_210;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_211);
lean_dec_ref(x_208);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_216 = x_212;
} else {
 lean_dec_ref(x_212);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
}
else
{
lean_dec_ref(x_203);
lean_dec_ref(x_202);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_204;
}
}
}
else
{
lean_dec_ref(x_173);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_172;
goto block_130;
}
}
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_172;
goto block_130;
}
}
else
{
lean_object* x_218; uint8_t x_219; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_218 = lean_st_ref_take(x_156);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 0);
lean_inc_ref(x_170);
x_221 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_220, x_1, x_170);
lean_ctor_set(x_218, 0, x_221);
x_222 = lean_st_ref_set(x_156, x_218);
lean_dec(x_156);
return x_168;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_218, 0);
x_224 = lean_ctor_get(x_218, 1);
x_225 = lean_ctor_get(x_218, 2);
x_226 = lean_ctor_get(x_218, 3);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_218);
lean_inc_ref(x_170);
x_227 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_223, x_1, x_170);
x_228 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_224);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_226);
x_229 = lean_st_ref_set(x_156, x_228);
lean_dec(x_156);
return x_168;
}
}
}
else
{
uint8_t x_230; 
x_230 = lean_ctor_get_uint8(x_170, sizeof(void*)*2);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_free_object(x_168);
x_231 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_170, 1);
lean_inc_ref(x_232);
lean_dec_ref(x_170);
x_29 = x_231;
x_30 = x_232;
x_31 = x_154;
x_32 = x_155;
x_33 = x_156;
x_34 = x_157;
x_35 = x_158;
x_36 = x_159;
x_37 = x_160;
x_38 = x_161;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_233; uint8_t x_234; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_233 = lean_st_ref_take(x_156);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc_ref(x_170);
x_236 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_235, x_1, x_170);
lean_ctor_set(x_233, 0, x_236);
x_237 = lean_st_ref_set(x_156, x_233);
lean_dec(x_156);
return x_168;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get(x_233, 0);
x_239 = lean_ctor_get(x_233, 1);
x_240 = lean_ctor_get(x_233, 2);
x_241 = lean_ctor_get(x_233, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_233);
lean_inc_ref(x_170);
x_242 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_238, x_1, x_170);
x_243 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_239);
lean_ctor_set(x_243, 2, x_240);
lean_ctor_set(x_243, 3, x_241);
x_244 = lean_st_ref_set(x_156, x_243);
lean_dec(x_156);
return x_168;
}
}
}
}
else
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_168, 0);
lean_inc(x_245);
lean_dec(x_168);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_245, 0);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec_ref(x_245);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_247 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_box(0);
if (lean_obj_tag(x_248) == 0)
{
uint8_t x_250; 
x_250 = lean_ctor_get_uint8(x_248, 0);
lean_dec_ref(x_248);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec_ref(x_247);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_251 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_249, x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_251;
goto block_130;
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_247;
goto block_130;
}
}
else
{
uint8_t x_252; 
x_252 = lean_ctor_get_uint8(x_248, sizeof(void*)*2);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec_ref(x_247);
x_253 = lean_ctor_get(x_248, 0);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_248, 1);
lean_inc_ref(x_254);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_255 = x_248;
} else {
 lean_dec_ref(x_248);
 x_255 = lean_box(0);
}
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_253);
x_256 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_249, x_253, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; lean_object* x_259; 
x_258 = lean_ctor_get_uint8(x_257, 0);
lean_dec_ref(x_257);
lean_inc_ref(x_254);
lean_inc_ref(x_253);
if (lean_is_scalar(x_255)) {
 x_259 = lean_alloc_ctor(1, 2, 1);
} else {
 x_259 = x_255;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set_uint8(x_259, sizeof(void*)*2, x_258);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_259;
x_71 = x_253;
x_72 = x_254;
x_73 = x_258;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_255);
x_260 = lean_ctor_get(x_257, 0);
lean_inc_ref(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc_ref(x_261);
x_262 = lean_ctor_get_uint8(x_257, sizeof(void*)*2);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_263 = x_257;
} else {
 lean_dec_ref(x_257);
 x_263 = lean_box(0);
}
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_260);
lean_inc_ref(x_1);
x_264 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_253, x_254, x_260, x_261, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec_ref(x_264);
lean_inc(x_265);
lean_inc_ref(x_260);
if (lean_is_scalar(x_263)) {
 x_266 = lean_alloc_ctor(1, 2, 1);
} else {
 x_266 = x_263;
}
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set_uint8(x_266, sizeof(void*)*2, x_262);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_266;
x_71 = x_260;
x_72 = x_265;
x_73 = x_262;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_263);
lean_dec_ref(x_260);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
x_267 = lean_ctor_get(x_264, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_268 = x_264;
} else {
 lean_dec_ref(x_264);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
return x_269;
}
}
}
else
{
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec_ref(x_253);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_256;
}
}
else
{
lean_dec_ref(x_248);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_247;
goto block_130;
}
}
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_247;
goto block_130;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_270 = lean_st_ref_take(x_156);
x_271 = lean_ctor_get(x_270, 0);
lean_inc_ref(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 3);
lean_inc_ref(x_274);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 x_275 = x_270;
} else {
 lean_dec_ref(x_270);
 x_275 = lean_box(0);
}
lean_inc_ref(x_245);
x_276 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_271, x_1, x_245);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 4, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_272);
lean_ctor_set(x_277, 2, x_273);
lean_ctor_set(x_277, 3, x_274);
x_278 = lean_st_ref_set(x_156, x_277);
lean_dec(x_156);
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_245);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_245, sizeof(void*)*2);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_281);
x_282 = lean_ctor_get(x_245, 1);
lean_inc_ref(x_282);
lean_dec_ref(x_245);
x_29 = x_281;
x_30 = x_282;
x_31 = x_154;
x_32 = x_155;
x_33 = x_156;
x_34 = x_157;
x_35 = x_158;
x_36 = x_159;
x_37 = x_160;
x_38 = x_161;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_283 = lean_st_ref_take(x_156);
x_284 = lean_ctor_get(x_283, 0);
lean_inc_ref(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 2);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 3);
lean_inc_ref(x_287);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 lean_ctor_release(x_283, 2);
 lean_ctor_release(x_283, 3);
 x_288 = x_283;
} else {
 lean_dec_ref(x_283);
 x_288 = lean_box(0);
}
lean_inc_ref(x_245);
x_289 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_284, x_1, x_245);
if (lean_is_scalar(x_288)) {
 x_290 = lean_alloc_ctor(0, 4, 0);
} else {
 x_290 = x_288;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
lean_ctor_set(x_290, 2, x_286);
lean_ctor_set(x_290, 3, x_287);
x_291 = lean_st_ref_set(x_156, x_290);
lean_dec(x_156);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_245);
return x_292;
}
}
}
}
else
{
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_168;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_163, 0);
x_294 = lean_ctor_get(x_163, 1);
x_295 = lean_ctor_get(x_163, 3);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_163);
x_296 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
lean_ctor_set(x_296, 2, x_153);
lean_ctor_set(x_296, 3, x_295);
x_297 = lean_st_ref_set(x_156, x_296);
x_298 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_298);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_299 = lean_apply_10(x_298, x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161, lean_box(0));
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_301 = x_299;
} else {
 lean_dec_ref(x_299);
 x_301 = lean_box(0);
}
if (lean_obj_tag(x_300) == 0)
{
uint8_t x_302; 
x_302 = lean_ctor_get_uint8(x_300, 0);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_301);
lean_dec_ref(x_300);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_303 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_box(0);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_306; 
x_306 = lean_ctor_get_uint8(x_304, 0);
lean_dec_ref(x_304);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec_ref(x_303);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_1);
x_307 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_305, x_1, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_307;
goto block_130;
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_303;
goto block_130;
}
}
else
{
uint8_t x_308; 
x_308 = lean_ctor_get_uint8(x_304, sizeof(void*)*2);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec_ref(x_303);
x_309 = lean_ctor_get(x_304, 0);
lean_inc_ref(x_309);
x_310 = lean_ctor_get(x_304, 1);
lean_inc_ref(x_310);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_311 = x_304;
} else {
 lean_dec_ref(x_304);
 x_311 = lean_box(0);
}
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_309);
x_312 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_305, x_309, x_154, x_155, x_156, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec_ref(x_312);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; lean_object* x_315; 
x_314 = lean_ctor_get_uint8(x_313, 0);
lean_dec_ref(x_313);
lean_inc_ref(x_310);
lean_inc_ref(x_309);
if (lean_is_scalar(x_311)) {
 x_315 = lean_alloc_ctor(1, 2, 1);
} else {
 x_315 = x_311;
}
lean_ctor_set(x_315, 0, x_309);
lean_ctor_set(x_315, 1, x_310);
lean_ctor_set_uint8(x_315, sizeof(void*)*2, x_314);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_315;
x_71 = x_309;
x_72 = x_310;
x_73 = x_314;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_311);
x_316 = lean_ctor_get(x_313, 0);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_313, 1);
lean_inc_ref(x_317);
x_318 = lean_ctor_get_uint8(x_313, sizeof(void*)*2);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_319 = x_313;
} else {
 lean_dec_ref(x_313);
 x_319 = lean_box(0);
}
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_316);
lean_inc_ref(x_1);
x_320 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_309, x_310, x_316, x_317, x_157, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
lean_inc(x_321);
lean_inc_ref(x_316);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(1, 2, 1);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_316);
lean_ctor_set(x_322, 1, x_321);
lean_ctor_set_uint8(x_322, sizeof(void*)*2, x_318);
x_62 = x_159;
x_63 = x_161;
x_64 = x_155;
x_65 = x_154;
x_66 = x_158;
x_67 = x_156;
x_68 = x_157;
x_69 = x_160;
x_70 = x_322;
x_71 = x_316;
x_72 = x_321;
x_73 = x_318;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_319);
lean_dec_ref(x_316);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
x_323 = lean_ctor_get(x_320, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_324 = x_320;
} else {
 lean_dec_ref(x_320);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_323);
return x_325;
}
}
}
else
{
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_312;
}
}
else
{
lean_dec_ref(x_304);
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_303;
goto block_130;
}
}
}
else
{
x_90 = x_159;
x_91 = x_161;
x_92 = x_155;
x_93 = x_154;
x_94 = x_158;
x_95 = x_156;
x_96 = x_157;
x_97 = x_160;
x_98 = x_303;
goto block_130;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_326 = lean_st_ref_take(x_156);
x_327 = lean_ctor_get(x_326, 0);
lean_inc_ref(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_326, 3);
lean_inc_ref(x_330);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_331 = x_326;
} else {
 lean_dec_ref(x_326);
 x_331 = lean_box(0);
}
lean_inc_ref(x_300);
x_332 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_327, x_1, x_300);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(0, 4, 0);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_328);
lean_ctor_set(x_333, 2, x_329);
lean_ctor_set(x_333, 3, x_330);
x_334 = lean_st_ref_set(x_156, x_333);
lean_dec(x_156);
if (lean_is_scalar(x_301)) {
 x_335 = lean_alloc_ctor(0, 1, 0);
} else {
 x_335 = x_301;
}
lean_ctor_set(x_335, 0, x_300);
return x_335;
}
}
else
{
uint8_t x_336; 
x_336 = lean_ctor_get_uint8(x_300, sizeof(void*)*2);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_301);
x_337 = lean_ctor_get(x_300, 0);
lean_inc_ref(x_337);
x_338 = lean_ctor_get(x_300, 1);
lean_inc_ref(x_338);
lean_dec_ref(x_300);
x_29 = x_337;
x_30 = x_338;
x_31 = x_154;
x_32 = x_155;
x_33 = x_156;
x_34 = x_157;
x_35 = x_158;
x_36 = x_159;
x_37 = x_160;
x_38 = x_161;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_155);
lean_dec(x_154);
x_339 = lean_st_ref_take(x_156);
x_340 = lean_ctor_get(x_339, 0);
lean_inc_ref(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_339, 3);
lean_inc_ref(x_343);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_344 = x_339;
} else {
 lean_dec_ref(x_339);
 x_344 = lean_box(0);
}
lean_inc_ref(x_300);
x_345 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_340, x_1, x_300);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 4, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_341);
lean_ctor_set(x_346, 2, x_342);
lean_ctor_set(x_346, 3, x_343);
x_347 = lean_st_ref_set(x_156, x_346);
lean_dec(x_156);
if (lean_is_scalar(x_301)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_301;
}
lean_ctor_set(x_348, 0, x_300);
return x_348;
}
}
}
else
{
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_1);
return x_299;
}
}
}
block_375:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_st_ref_get(x_354);
x_361 = lean_ctor_get(x_360, 0);
lean_inc_ref(x_361);
lean_dec(x_360);
x_362 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_361, x_1);
if (lean_obj_tag(x_362) == 1)
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_8);
lean_dec(x_151);
lean_dec_ref(x_1);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
if (lean_is_scalar(x_150)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_150;
}
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_362);
lean_dec(x_150);
x_365 = lean_nat_add(x_151, x_350);
lean_dec(x_151);
x_366 = lean_unsigned_to_nat(1000u);
x_367 = lean_nat_mod(x_365, x_366);
x_368 = lean_unsigned_to_nat(0u);
x_369 = lean_nat_dec_eq(x_367, x_368);
lean_dec(x_367);
if (x_369 == 0)
{
x_153 = x_365;
x_154 = x_352;
x_155 = x_353;
x_156 = x_354;
x_157 = x_355;
x_158 = x_356;
x_159 = x_357;
x_160 = x_8;
x_161 = x_358;
x_162 = lean_box(0);
goto block_349;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0;
x_371 = l_Lean_Core_checkSystem(x_370, x_8, x_358);
if (lean_obj_tag(x_371) == 0)
{
lean_dec_ref(x_371);
x_153 = x_365;
x_154 = x_352;
x_155 = x_353;
x_156 = x_354;
x_157 = x_355;
x_158 = x_356;
x_159 = x_357;
x_160 = x_8;
x_161 = x_358;
x_162 = lean_box(0);
goto block_349;
}
else
{
uint8_t x_372; 
lean_dec(x_365);
lean_dec(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
return x_371;
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
lean_dec(x_371);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_373);
return x_374;
}
}
}
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_147);
lean_free_object(x_8);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_148);
if (x_382 == 0)
{
return x_148;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_148, 0);
lean_inc(x_383);
lean_dec(x_148);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; 
lean_free_object(x_8);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_385 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_137);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; uint8_t x_402; 
x_386 = lean_ctor_get(x_8, 0);
x_387 = lean_ctor_get(x_8, 1);
x_388 = lean_ctor_get(x_8, 2);
x_389 = lean_ctor_get(x_8, 3);
x_390 = lean_ctor_get(x_8, 4);
x_391 = lean_ctor_get(x_8, 5);
x_392 = lean_ctor_get(x_8, 6);
x_393 = lean_ctor_get(x_8, 7);
x_394 = lean_ctor_get(x_8, 8);
x_395 = lean_ctor_get(x_8, 9);
x_396 = lean_ctor_get(x_8, 10);
x_397 = lean_ctor_get(x_8, 11);
x_398 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_399 = lean_ctor_get(x_8, 12);
x_400 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_401 = lean_ctor_get(x_8, 13);
lean_inc(x_401);
lean_inc(x_399);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_8);
x_402 = lean_nat_dec_eq(x_389, x_390);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_st_ref_get(x_4);
x_404 = l_Lean_Meta_Sym_Simp_getConfig___redArg(x_3);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_505; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
lean_dec(x_403);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
lean_dec(x_405);
x_478 = lean_unsigned_to_nat(1u);
x_479 = lean_nat_add(x_389, x_478);
lean_dec(x_389);
x_480 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_480, 0, x_386);
lean_ctor_set(x_480, 1, x_387);
lean_ctor_set(x_480, 2, x_388);
lean_ctor_set(x_480, 3, x_479);
lean_ctor_set(x_480, 4, x_390);
lean_ctor_set(x_480, 5, x_391);
lean_ctor_set(x_480, 6, x_392);
lean_ctor_set(x_480, 7, x_393);
lean_ctor_set(x_480, 8, x_394);
lean_ctor_set(x_480, 9, x_395);
lean_ctor_set(x_480, 10, x_396);
lean_ctor_set(x_480, 11, x_397);
lean_ctor_set(x_480, 12, x_399);
lean_ctor_set(x_480, 13, x_401);
lean_ctor_set_uint8(x_480, sizeof(void*)*14, x_398);
lean_ctor_set_uint8(x_480, sizeof(void*)*14 + 1, x_400);
x_505 = lean_nat_dec_le(x_408, x_407);
lean_dec(x_408);
if (x_505 == 0)
{
x_481 = x_2;
x_482 = x_3;
x_483 = x_4;
x_484 = x_5;
x_485 = x_6;
x_486 = x_7;
x_487 = x_9;
x_488 = lean_box(0);
goto block_504;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_506 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
x_507 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_506, x_6, x_7, x_480, x_9);
lean_dec(x_9);
lean_dec_ref(x_480);
lean_dec(x_7);
lean_dec_ref(x_6);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_509 = x_507;
} else {
 lean_dec_ref(x_507);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 1, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_508);
return x_510;
}
block_477:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_419 = lean_st_ref_take(x_412);
x_420 = lean_ctor_get(x_419, 0);
lean_inc_ref(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_419, 3);
lean_inc_ref(x_422);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_423 = x_419;
} else {
 lean_dec_ref(x_419);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 4, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_421);
lean_ctor_set(x_424, 2, x_409);
lean_ctor_set(x_424, 3, x_422);
x_425 = lean_st_ref_set(x_412, x_424);
x_426 = lean_ctor_get(x_410, 0);
lean_inc_ref(x_426);
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_1);
x_427 = lean_apply_10(x_426, x_1, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417, lean_box(0));
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
if (lean_obj_tag(x_428) == 0)
{
uint8_t x_430; 
x_430 = lean_ctor_get_uint8(x_428, 0);
if (x_430 == 0)
{
lean_object* x_431; 
lean_dec(x_429);
lean_dec_ref(x_428);
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_1);
x_431 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_box(0);
if (lean_obj_tag(x_432) == 0)
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_432, 0);
lean_dec_ref(x_432);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec_ref(x_431);
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_1);
x_435 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_433, x_1, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417);
x_90 = x_415;
x_91 = x_417;
x_92 = x_411;
x_93 = x_410;
x_94 = x_414;
x_95 = x_412;
x_96 = x_413;
x_97 = x_416;
x_98 = x_435;
goto block_130;
}
else
{
x_90 = x_415;
x_91 = x_417;
x_92 = x_411;
x_93 = x_410;
x_94 = x_414;
x_95 = x_412;
x_96 = x_413;
x_97 = x_416;
x_98 = x_431;
goto block_130;
}
}
else
{
uint8_t x_436; 
x_436 = lean_ctor_get_uint8(x_432, sizeof(void*)*2);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec_ref(x_431);
x_437 = lean_ctor_get(x_432, 0);
lean_inc_ref(x_437);
x_438 = lean_ctor_get(x_432, 1);
lean_inc_ref(x_438);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_439 = x_432;
} else {
 lean_dec_ref(x_432);
 x_439 = lean_box(0);
}
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc_ref(x_411);
lean_inc(x_410);
lean_inc_ref(x_437);
x_440 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_433, x_437, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
if (lean_obj_tag(x_441) == 0)
{
uint8_t x_442; lean_object* x_443; 
x_442 = lean_ctor_get_uint8(x_441, 0);
lean_dec_ref(x_441);
lean_inc_ref(x_438);
lean_inc_ref(x_437);
if (lean_is_scalar(x_439)) {
 x_443 = lean_alloc_ctor(1, 2, 1);
} else {
 x_443 = x_439;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_442);
x_62 = x_415;
x_63 = x_417;
x_64 = x_411;
x_65 = x_410;
x_66 = x_414;
x_67 = x_412;
x_68 = x_413;
x_69 = x_416;
x_70 = x_443;
x_71 = x_437;
x_72 = x_438;
x_73 = x_442;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_439);
x_444 = lean_ctor_get(x_441, 0);
lean_inc_ref(x_444);
x_445 = lean_ctor_get(x_441, 1);
lean_inc_ref(x_445);
x_446 = lean_ctor_get_uint8(x_441, sizeof(void*)*2);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_447 = x_441;
} else {
 lean_dec_ref(x_441);
 x_447 = lean_box(0);
}
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc_ref(x_444);
lean_inc_ref(x_1);
x_448 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_437, x_438, x_444, x_445, x_413, x_414, x_415, x_416, x_417);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
lean_inc(x_449);
lean_inc_ref(x_444);
if (lean_is_scalar(x_447)) {
 x_450 = lean_alloc_ctor(1, 2, 1);
} else {
 x_450 = x_447;
}
lean_ctor_set(x_450, 0, x_444);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*2, x_446);
x_62 = x_415;
x_63 = x_417;
x_64 = x_411;
x_65 = x_410;
x_66 = x_414;
x_67 = x_412;
x_68 = x_413;
x_69 = x_416;
x_70 = x_450;
x_71 = x_444;
x_72 = x_449;
x_73 = x_446;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_447);
lean_dec_ref(x_444);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_1);
x_451 = lean_ctor_get(x_448, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_452 = x_448;
} else {
 lean_dec_ref(x_448);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
}
else
{
lean_dec(x_439);
lean_dec_ref(x_438);
lean_dec_ref(x_437);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_1);
return x_440;
}
}
else
{
lean_dec_ref(x_432);
x_90 = x_415;
x_91 = x_417;
x_92 = x_411;
x_93 = x_410;
x_94 = x_414;
x_95 = x_412;
x_96 = x_413;
x_97 = x_416;
x_98 = x_431;
goto block_130;
}
}
}
else
{
x_90 = x_415;
x_91 = x_417;
x_92 = x_411;
x_93 = x_410;
x_94 = x_414;
x_95 = x_412;
x_96 = x_413;
x_97 = x_416;
x_98 = x_431;
goto block_130;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec(x_410);
x_454 = lean_st_ref_take(x_412);
x_455 = lean_ctor_get(x_454, 0);
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_454, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_454, 3);
lean_inc_ref(x_458);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 lean_ctor_release(x_454, 2);
 lean_ctor_release(x_454, 3);
 x_459 = x_454;
} else {
 lean_dec_ref(x_454);
 x_459 = lean_box(0);
}
lean_inc_ref(x_428);
x_460 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_455, x_1, x_428);
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(0, 4, 0);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_456);
lean_ctor_set(x_461, 2, x_457);
lean_ctor_set(x_461, 3, x_458);
x_462 = lean_st_ref_set(x_412, x_461);
lean_dec(x_412);
if (lean_is_scalar(x_429)) {
 x_463 = lean_alloc_ctor(0, 1, 0);
} else {
 x_463 = x_429;
}
lean_ctor_set(x_463, 0, x_428);
return x_463;
}
}
else
{
uint8_t x_464; 
x_464 = lean_ctor_get_uint8(x_428, sizeof(void*)*2);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_429);
x_465 = lean_ctor_get(x_428, 0);
lean_inc_ref(x_465);
x_466 = lean_ctor_get(x_428, 1);
lean_inc_ref(x_466);
lean_dec_ref(x_428);
x_29 = x_465;
x_30 = x_466;
x_31 = x_410;
x_32 = x_411;
x_33 = x_412;
x_34 = x_413;
x_35 = x_414;
x_36 = x_415;
x_37 = x_416;
x_38 = x_417;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec(x_410);
x_467 = lean_st_ref_take(x_412);
x_468 = lean_ctor_get(x_467, 0);
lean_inc_ref(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 2);
lean_inc(x_470);
x_471 = lean_ctor_get(x_467, 3);
lean_inc_ref(x_471);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_472 = x_467;
} else {
 lean_dec_ref(x_467);
 x_472 = lean_box(0);
}
lean_inc_ref(x_428);
x_473 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_468, x_1, x_428);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(0, 4, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_469);
lean_ctor_set(x_474, 2, x_470);
lean_ctor_set(x_474, 3, x_471);
x_475 = lean_st_ref_set(x_412, x_474);
lean_dec(x_412);
if (lean_is_scalar(x_429)) {
 x_476 = lean_alloc_ctor(0, 1, 0);
} else {
 x_476 = x_429;
}
lean_ctor_set(x_476, 0, x_428);
return x_476;
}
}
}
else
{
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_1);
return x_427;
}
}
block_504:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_st_ref_get(x_483);
x_490 = lean_ctor_get(x_489, 0);
lean_inc_ref(x_490);
lean_dec(x_489);
x_491 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_490, x_1);
if (lean_obj_tag(x_491) == 1)
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_407);
lean_dec_ref(x_1);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
lean_dec_ref(x_491);
if (lean_is_scalar(x_406)) {
 x_493 = lean_alloc_ctor(0, 1, 0);
} else {
 x_493 = x_406;
}
lean_ctor_set(x_493, 0, x_492);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
lean_dec(x_491);
lean_dec(x_406);
x_494 = lean_nat_add(x_407, x_478);
lean_dec(x_407);
x_495 = lean_unsigned_to_nat(1000u);
x_496 = lean_nat_mod(x_494, x_495);
x_497 = lean_unsigned_to_nat(0u);
x_498 = lean_nat_dec_eq(x_496, x_497);
lean_dec(x_496);
if (x_498 == 0)
{
x_409 = x_494;
x_410 = x_481;
x_411 = x_482;
x_412 = x_483;
x_413 = x_484;
x_414 = x_485;
x_415 = x_486;
x_416 = x_480;
x_417 = x_487;
x_418 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_499; lean_object* x_500; 
x_499 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0;
x_500 = l_Lean_Core_checkSystem(x_499, x_480, x_487);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_409 = x_494;
x_410 = x_481;
x_411 = x_482;
x_412 = x_483;
x_413 = x_484;
x_414 = x_485;
x_415 = x_486;
x_416 = x_480;
x_417 = x_487;
x_418 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_494);
lean_dec(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec_ref(x_1);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 x_502 = x_500;
} else {
 lean_dec_ref(x_500);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 1, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_501);
return x_503;
}
}
}
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_403);
lean_dec_ref(x_401);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec_ref(x_387);
lean_dec_ref(x_386);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_511 = lean_ctor_get(x_404, 0);
lean_inc(x_511);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_512 = x_404;
} else {
 lean_dec_ref(x_404);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 1, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_511);
return x_513;
}
}
else
{
lean_object* x_514; 
lean_dec_ref(x_401);
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_390);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec_ref(x_387);
lean_dec_ref(x_386);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_514 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_391);
return x_514;
}
}
block_28:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_take(x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_12);
x_17 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_16, x_1, x_12);
lean_ctor_set(x_14, 0, x_17);
x_18 = lean_st_ref_set(x_11, x_14);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 2);
x_23 = lean_ctor_get(x_14, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
lean_inc_ref(x_12);
x_24 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_20, x_1, x_12);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
x_26 = lean_st_ref_set(x_11, x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_12);
return x_27;
}
}
block_61:
{
lean_object* x_40; 
lean_inc(x_38);
lean_inc_ref(x_37);
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc_ref(x_29);
x_40 = lean_sym_simp(x_29, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
x_42 = lean_ctor_get_uint8(x_41, 0);
lean_dec_ref(x_41);
x_43 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_42);
x_11 = x_33;
x_12 = x_43;
x_13 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_45);
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_29, x_30, x_45, x_46, x_34, x_35, x_36, x_37, x_38);
lean_dec(x_34);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_ctor_set(x_41, 1, x_48);
x_11 = x_33;
x_12 = x_41;
x_13 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_49; 
lean_free_object(x_41);
lean_dec_ref(x_45);
lean_dec(x_33);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
x_54 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
lean_inc_ref(x_52);
lean_inc_ref(x_1);
x_55 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_29, x_30, x_52, x_53, x_34, x_35, x_36, x_37, x_38);
lean_dec(x_34);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_54);
x_11 = x_33;
x_12 = x_57;
x_13 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_52);
lean_dec(x_33);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
}
}
else
{
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_1);
return x_40;
}
}
block_89:
{
if (x_73 == 0)
{
lean_dec_ref(x_70);
x_29 = x_71;
x_30 = x_72;
x_31 = x_65;
x_32 = x_64;
x_33 = x_67;
x_34 = x_68;
x_35 = x_66;
x_36 = x_62;
x_37 = x_69;
x_38 = x_63;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_75 = lean_st_ref_take(x_67);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_70);
x_78 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_77, x_1, x_70);
lean_ctor_set(x_75, 0, x_78);
x_79 = lean_st_ref_set(x_67, x_75);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_70);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_75, 0);
x_82 = lean_ctor_get(x_75, 1);
x_83 = lean_ctor_get(x_75, 2);
x_84 = lean_ctor_get(x_75, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_75);
lean_inc_ref(x_70);
x_85 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_81, x_1, x_70);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
x_87 = lean_st_ref_set(x_67, x_86);
lean_dec(x_67);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_70);
return x_88;
}
}
}
block_130:
{
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_101 = lean_st_ref_take(x_95);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_100);
x_104 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_103, x_1, x_100);
lean_ctor_set(x_101, 0, x_104);
x_105 = lean_st_ref_set(x_95, x_101);
lean_dec(x_95);
return x_98;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
x_108 = lean_ctor_get(x_101, 2);
x_109 = lean_ctor_get(x_101, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
lean_inc_ref(x_100);
x_110 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_106, x_1, x_100);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_109);
x_112 = lean_st_ref_set(x_95, x_111);
lean_dec(x_95);
return x_98;
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_free_object(x_98);
x_113 = lean_ctor_get(x_100, 0);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_100, 1);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_100, sizeof(void*)*2);
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_100;
x_71 = x_113;
x_72 = x_114;
x_73 = x_115;
x_74 = lean_box(0);
goto block_89;
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
lean_dec(x_98);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_117 = lean_st_ref_take(x_95);
x_118 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 3);
lean_inc_ref(x_121);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_122 = x_117;
} else {
 lean_dec_ref(x_117);
 x_122 = lean_box(0);
}
lean_inc_ref(x_116);
x_123 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_118, x_1, x_116);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 4, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
lean_ctor_set(x_124, 2, x_120);
lean_ctor_set(x_124, 3, x_121);
x_125 = lean_st_ref_set(x_95, x_124);
lean_dec(x_95);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_116);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_128);
x_129 = lean_ctor_get_uint8(x_116, sizeof(void*)*2);
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_116;
x_71 = x_127;
x_72 = x_128;
x_73 = x_129;
x_74 = lean_box(0);
goto block_89;
}
}
}
else
{
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec_ref(x_1);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_sym_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__0);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__1);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__2);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__3);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep___closed__4);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_cacheResult___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0_spec__0___redArg___closed__2);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__1);
l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
