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
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6;
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
lean_object* x_1; 
x_1 = l_Lean_maxRecDepthErrorMessage;
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__5;
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
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6;
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
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_375; 
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
x_349 = lean_unsigned_to_nat(1u);
x_350 = lean_nat_add(x_135, x_349);
lean_dec(x_135);
lean_ctor_set(x_8, 3, x_350);
x_375 = lean_nat_dec_le(x_149, x_151);
lean_dec(x_149);
if (x_375 == 0)
{
x_351 = x_2;
x_352 = x_3;
x_353 = x_4;
x_354 = x_5;
x_355 = x_6;
x_356 = x_7;
x_357 = x_9;
x_358 = lean_box(0);
goto block_374;
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_376 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
x_377 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_376, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
return x_377;
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_379);
return x_380;
}
}
block_348:
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_st_ref_take(x_155);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_162, 2);
lean_dec(x_164);
lean_ctor_set(x_162, 2, x_152);
x_165 = lean_st_ref_set(x_155, x_162);
x_166 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_166);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_167 = lean_apply_10(x_166, x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160, lean_box(0));
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_167, 0);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = lean_ctor_get_uint8(x_169, 0);
if (x_170 == 0)
{
lean_object* x_171; 
lean_free_object(x_167);
lean_dec_ref(x_169);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_171 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_box(0);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_174; 
x_174 = lean_ctor_get_uint8(x_172, 0);
lean_dec_ref(x_172);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec_ref(x_171);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_175 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_173, x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_175;
goto block_130;
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_171;
goto block_130;
}
}
else
{
uint8_t x_176; 
x_176 = lean_ctor_get_uint8(x_172, sizeof(void*)*2);
if (x_176 == 0)
{
uint8_t x_177; 
lean_dec_ref(x_171);
x_177 = !lean_is_exclusive(x_172);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_178);
x_180 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_173, x_178, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = lean_ctor_get_uint8(x_181, 0);
lean_dec_ref(x_181);
lean_inc_ref(x_179);
lean_inc_ref(x_178);
lean_ctor_set_uint8(x_172, sizeof(void*)*2, x_182);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_172;
x_71 = x_178;
x_72 = x_179;
x_73 = x_182;
x_74 = lean_box(0);
goto block_89;
}
else
{
uint8_t x_183; 
lean_free_object(x_172);
x_183 = !lean_is_exclusive(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_181, 0);
x_185 = lean_ctor_get(x_181, 1);
x_186 = lean_ctor_get_uint8(x_181, sizeof(void*)*2);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_184);
lean_inc_ref(x_1);
x_187 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_178, x_179, x_184, x_185, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
lean_inc(x_188);
lean_inc_ref(x_184);
lean_ctor_set(x_181, 1, x_188);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_181;
x_71 = x_184;
x_72 = x_188;
x_73 = x_186;
x_74 = lean_box(0);
goto block_89;
}
else
{
uint8_t x_189; 
lean_free_object(x_181);
lean_dec_ref(x_184);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
x_189 = !lean_is_exclusive(x_187);
if (x_189 == 0)
{
return x_187;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_181, 0);
x_193 = lean_ctor_get(x_181, 1);
x_194 = lean_ctor_get_uint8(x_181, sizeof(void*)*2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_181);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_192);
lean_inc_ref(x_1);
x_195 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_178, x_179, x_192, x_193, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
lean_inc(x_196);
lean_inc_ref(x_192);
x_197 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_194);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_197;
x_71 = x_192;
x_72 = x_196;
x_73 = x_194;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec_ref(x_192);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_199 = x_195;
} else {
 lean_dec_ref(x_195);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
}
}
else
{
lean_free_object(x_172);
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_180;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_172, 0);
x_202 = lean_ctor_get(x_172, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_172);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_201);
x_203 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_173, x_201, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; lean_object* x_206; 
x_205 = lean_ctor_get_uint8(x_204, 0);
lean_dec_ref(x_204);
lean_inc_ref(x_202);
lean_inc_ref(x_201);
x_206 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_202);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_205);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_206;
x_71 = x_201;
x_72 = x_202;
x_73 = x_205;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_204, 0);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_204, 1);
lean_inc_ref(x_208);
x_209 = lean_ctor_get_uint8(x_204, sizeof(void*)*2);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_210 = x_204;
} else {
 lean_dec_ref(x_204);
 x_210 = lean_box(0);
}
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_207);
lean_inc_ref(x_1);
x_211 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_201, x_202, x_207, x_208, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
lean_inc(x_212);
lean_inc_ref(x_207);
if (lean_is_scalar(x_210)) {
 x_213 = lean_alloc_ctor(1, 2, 1);
} else {
 x_213 = x_210;
}
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*2, x_209);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_213;
x_71 = x_207;
x_72 = x_212;
x_73 = x_209;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_210);
lean_dec_ref(x_207);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_215 = x_211;
} else {
 lean_dec_ref(x_211);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
}
else
{
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_203;
}
}
}
else
{
lean_dec_ref(x_172);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_171;
goto block_130;
}
}
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_171;
goto block_130;
}
}
else
{
lean_object* x_217; uint8_t x_218; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_217 = lean_st_ref_take(x_155);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
lean_inc_ref(x_169);
x_220 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_219, x_1, x_169);
lean_ctor_set(x_217, 0, x_220);
x_221 = lean_st_ref_set(x_155, x_217);
lean_dec(x_155);
return x_167;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_217, 0);
x_223 = lean_ctor_get(x_217, 1);
x_224 = lean_ctor_get(x_217, 2);
x_225 = lean_ctor_get(x_217, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_217);
lean_inc_ref(x_169);
x_226 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_222, x_1, x_169);
x_227 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_223);
lean_ctor_set(x_227, 2, x_224);
lean_ctor_set(x_227, 3, x_225);
x_228 = lean_st_ref_set(x_155, x_227);
lean_dec(x_155);
return x_167;
}
}
}
else
{
uint8_t x_229; 
x_229 = lean_ctor_get_uint8(x_169, sizeof(void*)*2);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_free_object(x_167);
x_230 = lean_ctor_get(x_169, 0);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_169, 1);
lean_inc_ref(x_231);
lean_dec_ref(x_169);
x_29 = x_230;
x_30 = x_231;
x_31 = x_153;
x_32 = x_154;
x_33 = x_155;
x_34 = x_156;
x_35 = x_157;
x_36 = x_158;
x_37 = x_159;
x_38 = x_160;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_232; uint8_t x_233; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_232 = lean_st_ref_take(x_155);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc_ref(x_169);
x_235 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_234, x_1, x_169);
lean_ctor_set(x_232, 0, x_235);
x_236 = lean_st_ref_set(x_155, x_232);
lean_dec(x_155);
return x_167;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_232, 0);
x_238 = lean_ctor_get(x_232, 1);
x_239 = lean_ctor_get(x_232, 2);
x_240 = lean_ctor_get(x_232, 3);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_232);
lean_inc_ref(x_169);
x_241 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_237, x_1, x_169);
x_242 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
lean_ctor_set(x_242, 2, x_239);
lean_ctor_set(x_242, 3, x_240);
x_243 = lean_st_ref_set(x_155, x_242);
lean_dec(x_155);
return x_167;
}
}
}
}
else
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_167, 0);
lean_inc(x_244);
lean_dec(x_167);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
x_245 = lean_ctor_get_uint8(x_244, 0);
if (x_245 == 0)
{
lean_object* x_246; 
lean_dec_ref(x_244);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_246 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_box(0);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_249; 
x_249 = lean_ctor_get_uint8(x_247, 0);
lean_dec_ref(x_247);
if (x_249 == 0)
{
lean_object* x_250; 
lean_dec_ref(x_246);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_250 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_248, x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_250;
goto block_130;
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_246;
goto block_130;
}
}
else
{
uint8_t x_251; 
x_251 = lean_ctor_get_uint8(x_247, sizeof(void*)*2);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_246);
x_252 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_252);
x_253 = lean_ctor_get(x_247, 1);
lean_inc_ref(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_252);
x_255 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_248, x_252, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; lean_object* x_258; 
x_257 = lean_ctor_get_uint8(x_256, 0);
lean_dec_ref(x_256);
lean_inc_ref(x_253);
lean_inc_ref(x_252);
if (lean_is_scalar(x_254)) {
 x_258 = lean_alloc_ctor(1, 2, 1);
} else {
 x_258 = x_254;
}
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*2, x_257);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_258;
x_71 = x_252;
x_72 = x_253;
x_73 = x_257;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_254);
x_259 = lean_ctor_get(x_256, 0);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_256, 1);
lean_inc_ref(x_260);
x_261 = lean_ctor_get_uint8(x_256, sizeof(void*)*2);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_262 = x_256;
} else {
 lean_dec_ref(x_256);
 x_262 = lean_box(0);
}
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_259);
lean_inc_ref(x_1);
x_263 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_252, x_253, x_259, x_260, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
lean_inc(x_264);
lean_inc_ref(x_259);
if (lean_is_scalar(x_262)) {
 x_265 = lean_alloc_ctor(1, 2, 1);
} else {
 x_265 = x_262;
}
lean_ctor_set(x_265, 0, x_259);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set_uint8(x_265, sizeof(void*)*2, x_261);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_265;
x_71 = x_259;
x_72 = x_264;
x_73 = x_261;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_262);
lean_dec_ref(x_259);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
x_266 = lean_ctor_get(x_263, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_267 = x_263;
} else {
 lean_dec_ref(x_263);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 1, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_266);
return x_268;
}
}
}
else
{
lean_dec(x_254);
lean_dec_ref(x_253);
lean_dec_ref(x_252);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_255;
}
}
else
{
lean_dec_ref(x_247);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_246;
goto block_130;
}
}
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_246;
goto block_130;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_269 = lean_st_ref_take(x_155);
x_270 = lean_ctor_get(x_269, 0);
lean_inc_ref(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 3);
lean_inc_ref(x_273);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 x_274 = x_269;
} else {
 lean_dec_ref(x_269);
 x_274 = lean_box(0);
}
lean_inc_ref(x_244);
x_275 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_270, x_1, x_244);
if (lean_is_scalar(x_274)) {
 x_276 = lean_alloc_ctor(0, 4, 0);
} else {
 x_276 = x_274;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_271);
lean_ctor_set(x_276, 2, x_272);
lean_ctor_set(x_276, 3, x_273);
x_277 = lean_st_ref_set(x_155, x_276);
lean_dec(x_155);
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_244);
return x_278;
}
}
else
{
uint8_t x_279; 
x_279 = lean_ctor_get_uint8(x_244, sizeof(void*)*2);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_244, 0);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_244, 1);
lean_inc_ref(x_281);
lean_dec_ref(x_244);
x_29 = x_280;
x_30 = x_281;
x_31 = x_153;
x_32 = x_154;
x_33 = x_155;
x_34 = x_156;
x_35 = x_157;
x_36 = x_158;
x_37 = x_159;
x_38 = x_160;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_282 = lean_st_ref_take(x_155);
x_283 = lean_ctor_get(x_282, 0);
lean_inc_ref(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_282, 3);
lean_inc_ref(x_286);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 x_287 = x_282;
} else {
 lean_dec_ref(x_282);
 x_287 = lean_box(0);
}
lean_inc_ref(x_244);
x_288 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_283, x_1, x_244);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_284);
lean_ctor_set(x_289, 2, x_285);
lean_ctor_set(x_289, 3, x_286);
x_290 = lean_st_ref_set(x_155, x_289);
lean_dec(x_155);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_244);
return x_291;
}
}
}
}
else
{
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_167;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_292 = lean_ctor_get(x_162, 0);
x_293 = lean_ctor_get(x_162, 1);
x_294 = lean_ctor_get(x_162, 3);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_162);
x_295 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_152);
lean_ctor_set(x_295, 3, x_294);
x_296 = lean_st_ref_set(x_155, x_295);
x_297 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_297);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_298 = lean_apply_10(x_297, x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160, lean_box(0));
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_300 = x_298;
} else {
 lean_dec_ref(x_298);
 x_300 = lean_box(0);
}
if (lean_obj_tag(x_299) == 0)
{
uint8_t x_301; 
x_301 = lean_ctor_get_uint8(x_299, 0);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_300);
lean_dec_ref(x_299);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_302 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_box(0);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_305; 
x_305 = lean_ctor_get_uint8(x_303, 0);
lean_dec_ref(x_303);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec_ref(x_302);
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_1);
x_306 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_304, x_1, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_306;
goto block_130;
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_302;
goto block_130;
}
}
else
{
uint8_t x_307; 
x_307 = lean_ctor_get_uint8(x_303, sizeof(void*)*2);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec_ref(x_302);
x_308 = lean_ctor_get(x_303, 0);
lean_inc_ref(x_308);
x_309 = lean_ctor_get(x_303, 1);
lean_inc_ref(x_309);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_310 = x_303;
} else {
 lean_dec_ref(x_303);
 x_310 = lean_box(0);
}
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_308);
x_311 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_304, x_308, x_153, x_154, x_155, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec_ref(x_311);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; lean_object* x_314; 
x_313 = lean_ctor_get_uint8(x_312, 0);
lean_dec_ref(x_312);
lean_inc_ref(x_309);
lean_inc_ref(x_308);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(1, 2, 1);
} else {
 x_314 = x_310;
}
lean_ctor_set(x_314, 0, x_308);
lean_ctor_set(x_314, 1, x_309);
lean_ctor_set_uint8(x_314, sizeof(void*)*2, x_313);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_314;
x_71 = x_308;
x_72 = x_309;
x_73 = x_313;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_310);
x_315 = lean_ctor_get(x_312, 0);
lean_inc_ref(x_315);
x_316 = lean_ctor_get(x_312, 1);
lean_inc_ref(x_316);
x_317 = lean_ctor_get_uint8(x_312, sizeof(void*)*2);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_318 = x_312;
} else {
 lean_dec_ref(x_312);
 x_318 = lean_box(0);
}
lean_inc(x_160);
lean_inc_ref(x_159);
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_315);
lean_inc_ref(x_1);
x_319 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_308, x_309, x_315, x_316, x_156, x_157, x_158, x_159, x_160);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec_ref(x_319);
lean_inc(x_320);
lean_inc_ref(x_315);
if (lean_is_scalar(x_318)) {
 x_321 = lean_alloc_ctor(1, 2, 1);
} else {
 x_321 = x_318;
}
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*2, x_317);
x_62 = x_158;
x_63 = x_160;
x_64 = x_154;
x_65 = x_153;
x_66 = x_157;
x_67 = x_155;
x_68 = x_156;
x_69 = x_159;
x_70 = x_321;
x_71 = x_315;
x_72 = x_320;
x_73 = x_317;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_318);
lean_dec_ref(x_315);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
x_322 = lean_ctor_get(x_319, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_323 = x_319;
} else {
 lean_dec_ref(x_319);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
}
}
else
{
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec_ref(x_308);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_311;
}
}
else
{
lean_dec_ref(x_303);
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_302;
goto block_130;
}
}
}
else
{
x_90 = x_158;
x_91 = x_160;
x_92 = x_154;
x_93 = x_153;
x_94 = x_157;
x_95 = x_155;
x_96 = x_156;
x_97 = x_159;
x_98 = x_302;
goto block_130;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_325 = lean_st_ref_take(x_155);
x_326 = lean_ctor_get(x_325, 0);
lean_inc_ref(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_325, 2);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 3);
lean_inc_ref(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
lean_inc_ref(x_299);
x_331 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_326, x_1, x_299);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 4, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_327);
lean_ctor_set(x_332, 2, x_328);
lean_ctor_set(x_332, 3, x_329);
x_333 = lean_st_ref_set(x_155, x_332);
lean_dec(x_155);
if (lean_is_scalar(x_300)) {
 x_334 = lean_alloc_ctor(0, 1, 0);
} else {
 x_334 = x_300;
}
lean_ctor_set(x_334, 0, x_299);
return x_334;
}
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_299, sizeof(void*)*2);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_300);
x_336 = lean_ctor_get(x_299, 0);
lean_inc_ref(x_336);
x_337 = lean_ctor_get(x_299, 1);
lean_inc_ref(x_337);
lean_dec_ref(x_299);
x_29 = x_336;
x_30 = x_337;
x_31 = x_153;
x_32 = x_154;
x_33 = x_155;
x_34 = x_156;
x_35 = x_157;
x_36 = x_158;
x_37 = x_159;
x_38 = x_160;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_154);
lean_dec(x_153);
x_338 = lean_st_ref_take(x_155);
x_339 = lean_ctor_get(x_338, 0);
lean_inc_ref(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 3);
lean_inc_ref(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
lean_inc_ref(x_299);
x_344 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_339, x_1, x_299);
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(0, 4, 0);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_340);
lean_ctor_set(x_345, 2, x_341);
lean_ctor_set(x_345, 3, x_342);
x_346 = lean_st_ref_set(x_155, x_345);
lean_dec(x_155);
if (lean_is_scalar(x_300)) {
 x_347 = lean_alloc_ctor(0, 1, 0);
} else {
 x_347 = x_300;
}
lean_ctor_set(x_347, 0, x_299);
return x_347;
}
}
}
else
{
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_1);
return x_298;
}
}
}
block_374:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_st_ref_get(x_353);
x_360 = lean_ctor_get(x_359, 0);
lean_inc_ref(x_360);
lean_dec(x_359);
x_361 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_360, x_1);
if (lean_obj_tag(x_361) == 1)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_351);
lean_dec_ref(x_8);
lean_dec(x_151);
lean_dec_ref(x_1);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec_ref(x_361);
if (lean_is_scalar(x_150)) {
 x_363 = lean_alloc_ctor(0, 1, 0);
} else {
 x_363 = x_150;
}
lean_ctor_set(x_363, 0, x_362);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_361);
lean_dec(x_150);
x_364 = lean_nat_add(x_151, x_349);
lean_dec(x_151);
x_365 = lean_unsigned_to_nat(1000u);
x_366 = lean_nat_mod(x_364, x_365);
x_367 = lean_unsigned_to_nat(0u);
x_368 = lean_nat_dec_eq(x_366, x_367);
lean_dec(x_366);
if (x_368 == 0)
{
x_152 = x_364;
x_153 = x_351;
x_154 = x_352;
x_155 = x_353;
x_156 = x_354;
x_157 = x_355;
x_158 = x_356;
x_159 = x_8;
x_160 = x_357;
x_161 = lean_box(0);
goto block_348;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0;
x_370 = l_Lean_Core_checkSystem(x_369, x_8, x_357);
if (lean_obj_tag(x_370) == 0)
{
lean_dec_ref(x_370);
x_152 = x_364;
x_153 = x_351;
x_154 = x_352;
x_155 = x_353;
x_156 = x_354;
x_157 = x_355;
x_158 = x_356;
x_159 = x_8;
x_160 = x_357;
x_161 = lean_box(0);
goto block_348;
}
else
{
uint8_t x_371; 
lean_dec(x_364);
lean_dec(x_357);
lean_dec(x_356);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_351);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
return x_370;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
}
}
}
else
{
uint8_t x_381; 
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
x_381 = !lean_is_exclusive(x_148);
if (x_381 == 0)
{
return x_148;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_148, 0);
lean_inc(x_382);
lean_dec(x_148);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
else
{
lean_object* x_384; 
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
x_384 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_137);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; uint8_t x_401; 
x_385 = lean_ctor_get(x_8, 0);
x_386 = lean_ctor_get(x_8, 1);
x_387 = lean_ctor_get(x_8, 2);
x_388 = lean_ctor_get(x_8, 3);
x_389 = lean_ctor_get(x_8, 4);
x_390 = lean_ctor_get(x_8, 5);
x_391 = lean_ctor_get(x_8, 6);
x_392 = lean_ctor_get(x_8, 7);
x_393 = lean_ctor_get(x_8, 8);
x_394 = lean_ctor_get(x_8, 9);
x_395 = lean_ctor_get(x_8, 10);
x_396 = lean_ctor_get(x_8, 11);
x_397 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_398 = lean_ctor_get(x_8, 12);
x_399 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_400 = lean_ctor_get(x_8, 13);
lean_inc(x_400);
lean_inc(x_398);
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
lean_inc(x_385);
lean_dec(x_8);
x_401 = lean_nat_dec_eq(x_388, x_389);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_st_ref_get(x_4);
x_403 = l_Lean_Meta_Sym_Simp_getConfig___redArg(x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_503; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_402, 2);
lean_inc(x_406);
lean_dec(x_402);
x_476 = lean_unsigned_to_nat(1u);
x_477 = lean_nat_add(x_388, x_476);
lean_dec(x_388);
x_478 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_478, 0, x_385);
lean_ctor_set(x_478, 1, x_386);
lean_ctor_set(x_478, 2, x_387);
lean_ctor_set(x_478, 3, x_477);
lean_ctor_set(x_478, 4, x_389);
lean_ctor_set(x_478, 5, x_390);
lean_ctor_set(x_478, 6, x_391);
lean_ctor_set(x_478, 7, x_392);
lean_ctor_set(x_478, 8, x_393);
lean_ctor_set(x_478, 9, x_394);
lean_ctor_set(x_478, 10, x_395);
lean_ctor_set(x_478, 11, x_396);
lean_ctor_set(x_478, 12, x_398);
lean_ctor_set(x_478, 13, x_400);
lean_ctor_set_uint8(x_478, sizeof(void*)*14, x_397);
lean_ctor_set_uint8(x_478, sizeof(void*)*14 + 1, x_399);
x_503 = lean_nat_dec_le(x_404, x_406);
lean_dec(x_404);
if (x_503 == 0)
{
x_479 = x_2;
x_480 = x_3;
x_481 = x_4;
x_482 = x_5;
x_483 = x_6;
x_484 = x_7;
x_485 = x_9;
x_486 = lean_box(0);
goto block_502;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_504 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__2;
x_505 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep_spec__1___redArg(x_504, x_6, x_7, x_478, x_9);
lean_dec(x_9);
lean_dec_ref(x_478);
lean_dec(x_7);
lean_dec_ref(x_6);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 1, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_506);
return x_508;
}
block_475:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_417 = lean_st_ref_take(x_410);
x_418 = lean_ctor_get(x_417, 0);
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_417, 3);
lean_inc_ref(x_420);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_421 = x_417;
} else {
 lean_dec_ref(x_417);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 4, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_418);
lean_ctor_set(x_422, 1, x_419);
lean_ctor_set(x_422, 2, x_407);
lean_ctor_set(x_422, 3, x_420);
x_423 = lean_st_ref_set(x_410, x_422);
x_424 = lean_ctor_get(x_408, 0);
lean_inc_ref(x_424);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc_ref(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc(x_408);
lean_inc_ref(x_1);
x_425 = lean_apply_10(x_424, x_1, x_408, x_409, x_410, x_411, x_412, x_413, x_414, x_415, lean_box(0));
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_427 = x_425;
} else {
 lean_dec_ref(x_425);
 x_427 = lean_box(0);
}
if (lean_obj_tag(x_426) == 0)
{
uint8_t x_428; 
x_428 = lean_ctor_get_uint8(x_426, 0);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_427);
lean_dec_ref(x_426);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc_ref(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc(x_408);
lean_inc_ref(x_1);
x_429 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpStep(x_1, x_408, x_409, x_410, x_411, x_412, x_413, x_414, x_415);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_box(0);
if (lean_obj_tag(x_430) == 0)
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_430, 0);
lean_dec_ref(x_430);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec_ref(x_429);
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc_ref(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc(x_408);
lean_inc_ref(x_1);
x_433 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_431, x_1, x_408, x_409, x_410, x_411, x_412, x_413, x_414, x_415);
x_90 = x_413;
x_91 = x_415;
x_92 = x_409;
x_93 = x_408;
x_94 = x_412;
x_95 = x_410;
x_96 = x_411;
x_97 = x_414;
x_98 = x_433;
goto block_130;
}
else
{
x_90 = x_413;
x_91 = x_415;
x_92 = x_409;
x_93 = x_408;
x_94 = x_412;
x_95 = x_410;
x_96 = x_411;
x_97 = x_414;
x_98 = x_429;
goto block_130;
}
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_430, sizeof(void*)*2);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec_ref(x_429);
x_435 = lean_ctor_get(x_430, 0);
lean_inc_ref(x_435);
x_436 = lean_ctor_get(x_430, 1);
lean_inc_ref(x_436);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_437 = x_430;
} else {
 lean_dec_ref(x_430);
 x_437 = lean_box(0);
}
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc_ref(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc_ref(x_409);
lean_inc(x_408);
lean_inc_ref(x_435);
x_438 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___lam__0(x_431, x_435, x_408, x_409, x_410, x_411, x_412, x_413, x_414, x_415);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
lean_dec_ref(x_438);
if (lean_obj_tag(x_439) == 0)
{
uint8_t x_440; lean_object* x_441; 
x_440 = lean_ctor_get_uint8(x_439, 0);
lean_dec_ref(x_439);
lean_inc_ref(x_436);
lean_inc_ref(x_435);
if (lean_is_scalar(x_437)) {
 x_441 = lean_alloc_ctor(1, 2, 1);
} else {
 x_441 = x_437;
}
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_436);
lean_ctor_set_uint8(x_441, sizeof(void*)*2, x_440);
x_62 = x_413;
x_63 = x_415;
x_64 = x_409;
x_65 = x_408;
x_66 = x_412;
x_67 = x_410;
x_68 = x_411;
x_69 = x_414;
x_70 = x_441;
x_71 = x_435;
x_72 = x_436;
x_73 = x_440;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_437);
x_442 = lean_ctor_get(x_439, 0);
lean_inc_ref(x_442);
x_443 = lean_ctor_get(x_439, 1);
lean_inc_ref(x_443);
x_444 = lean_ctor_get_uint8(x_439, sizeof(void*)*2);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_445 = x_439;
} else {
 lean_dec_ref(x_439);
 x_445 = lean_box(0);
}
lean_inc(x_415);
lean_inc_ref(x_414);
lean_inc(x_413);
lean_inc_ref(x_412);
lean_inc_ref(x_442);
lean_inc_ref(x_1);
x_446 = l_Lean_Meta_Sym_Simp_mkEqTrans(x_1, x_435, x_436, x_442, x_443, x_411, x_412, x_413, x_414, x_415);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
lean_inc(x_447);
lean_inc_ref(x_442);
if (lean_is_scalar(x_445)) {
 x_448 = lean_alloc_ctor(1, 2, 1);
} else {
 x_448 = x_445;
}
lean_ctor_set(x_448, 0, x_442);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set_uint8(x_448, sizeof(void*)*2, x_444);
x_62 = x_413;
x_63 = x_415;
x_64 = x_409;
x_65 = x_408;
x_66 = x_412;
x_67 = x_410;
x_68 = x_411;
x_69 = x_414;
x_70 = x_448;
x_71 = x_442;
x_72 = x_447;
x_73 = x_444;
x_74 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_445);
lean_dec_ref(x_442);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_1);
x_449 = lean_ctor_get(x_446, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_450 = x_446;
} else {
 lean_dec_ref(x_446);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
}
else
{
lean_dec(x_437);
lean_dec_ref(x_436);
lean_dec_ref(x_435);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_1);
return x_438;
}
}
else
{
lean_dec_ref(x_430);
x_90 = x_413;
x_91 = x_415;
x_92 = x_409;
x_93 = x_408;
x_94 = x_412;
x_95 = x_410;
x_96 = x_411;
x_97 = x_414;
x_98 = x_429;
goto block_130;
}
}
}
else
{
x_90 = x_413;
x_91 = x_415;
x_92 = x_409;
x_93 = x_408;
x_94 = x_412;
x_95 = x_410;
x_96 = x_411;
x_97 = x_414;
x_98 = x_429;
goto block_130;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_409);
lean_dec(x_408);
x_452 = lean_st_ref_take(x_410);
x_453 = lean_ctor_get(x_452, 0);
lean_inc_ref(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_452, 3);
lean_inc_ref(x_456);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 lean_ctor_release(x_452, 3);
 x_457 = x_452;
} else {
 lean_dec_ref(x_452);
 x_457 = lean_box(0);
}
lean_inc_ref(x_426);
x_458 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_453, x_1, x_426);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(0, 4, 0);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
x_460 = lean_st_ref_set(x_410, x_459);
lean_dec(x_410);
if (lean_is_scalar(x_427)) {
 x_461 = lean_alloc_ctor(0, 1, 0);
} else {
 x_461 = x_427;
}
lean_ctor_set(x_461, 0, x_426);
return x_461;
}
}
else
{
uint8_t x_462; 
x_462 = lean_ctor_get_uint8(x_426, sizeof(void*)*2);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_427);
x_463 = lean_ctor_get(x_426, 0);
lean_inc_ref(x_463);
x_464 = lean_ctor_get(x_426, 1);
lean_inc_ref(x_464);
lean_dec_ref(x_426);
x_29 = x_463;
x_30 = x_464;
x_31 = x_408;
x_32 = x_409;
x_33 = x_410;
x_34 = x_411;
x_35 = x_412;
x_36 = x_413;
x_37 = x_414;
x_38 = x_415;
x_39 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec_ref(x_409);
lean_dec(x_408);
x_465 = lean_st_ref_take(x_410);
x_466 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_465, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 3);
lean_inc_ref(x_469);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_470 = x_465;
} else {
 lean_dec_ref(x_465);
 x_470 = lean_box(0);
}
lean_inc_ref(x_426);
x_471 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__0___redArg(x_466, x_1, x_426);
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(0, 4, 0);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_467);
lean_ctor_set(x_472, 2, x_468);
lean_ctor_set(x_472, 3, x_469);
x_473 = lean_st_ref_set(x_410, x_472);
lean_dec(x_410);
if (lean_is_scalar(x_427)) {
 x_474 = lean_alloc_ctor(0, 1, 0);
} else {
 x_474 = x_427;
}
lean_ctor_set(x_474, 0, x_426);
return x_474;
}
}
}
else
{
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_1);
return x_425;
}
}
block_502:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_st_ref_get(x_481);
x_488 = lean_ctor_get(x_487, 0);
lean_inc_ref(x_488);
lean_dec(x_487);
x_489 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__1___redArg(x_488, x_1);
if (lean_obj_tag(x_489) == 1)
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_485);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_406);
lean_dec_ref(x_1);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
lean_dec_ref(x_489);
if (lean_is_scalar(x_405)) {
 x_491 = lean_alloc_ctor(0, 1, 0);
} else {
 x_491 = x_405;
}
lean_ctor_set(x_491, 0, x_490);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
lean_dec(x_489);
lean_dec(x_405);
x_492 = lean_nat_add(x_406, x_476);
lean_dec(x_406);
x_493 = lean_unsigned_to_nat(1000u);
x_494 = lean_nat_mod(x_492, x_493);
x_495 = lean_unsigned_to_nat(0u);
x_496 = lean_nat_dec_eq(x_494, x_495);
lean_dec(x_494);
if (x_496 == 0)
{
x_407 = x_492;
x_408 = x_479;
x_409 = x_480;
x_410 = x_481;
x_411 = x_482;
x_412 = x_483;
x_413 = x_484;
x_414 = x_478;
x_415 = x_485;
x_416 = lean_box(0);
goto block_475;
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = l___private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl___closed__0;
x_498 = l_Lean_Core_checkSystem(x_497, x_478, x_485);
if (lean_obj_tag(x_498) == 0)
{
lean_dec_ref(x_498);
x_407 = x_492;
x_408 = x_479;
x_409 = x_480;
x_410 = x_481;
x_411 = x_482;
x_412 = x_483;
x_413 = x_484;
x_414 = x_478;
x_415 = x_485;
x_416 = lean_box(0);
goto block_475;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_492);
lean_dec(x_485);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec_ref(x_1);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 1, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_499);
return x_501;
}
}
}
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_402);
lean_dec_ref(x_400);
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_388);
lean_dec_ref(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_385);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_403, 0);
lean_inc(x_509);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_510 = x_403;
} else {
 lean_dec_ref(x_403);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 1, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_509);
return x_511;
}
}
else
{
lean_object* x_512; 
lean_dec_ref(x_400);
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_389);
lean_dec(x_388);
lean_dec_ref(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_385);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_512 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg(x_390);
return x_512;
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
l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Simp_Main_0__Lean_Meta_Sym_Simp_simpImpl_spec__2___redArg___closed__6);
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
