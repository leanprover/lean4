// Lean compiler output
// Module: Lean.LocalContext
// Imports: public import Init.Data.Nat.Control public import Lean.Data.PersistentArray public import Lean.Expr import Init.Data.ToString.Macro import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.default"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__1 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__1_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.LocalDeclKind.implDetail"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__2 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__3 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__3_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.auxDecl"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__4 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__5 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__6;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLocalDeclKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLocalDeclKind = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableLocalDeclKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLocalDeclKind = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedLocalDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedLocalDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl;
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalDecl_isAuxDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isAuxDecl___closed__0;
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalDecl_isImplementationDetail___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isImplementationDetail___closed__0;
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_value___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.LocalContext"};
static const lean_object* l_Lean_LocalDecl_value___closed__0 = (const lean_object*)&l_Lean_LocalDecl_value___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.LocalDecl.value"};
static const lean_object* l_Lean_LocalDecl_value___closed__1 = (const lean_object*)&l_Lean_LocalDecl_value___closed__1_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__2 = (const lean_object*)&l_Lean_LocalDecl_value___closed__2_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__3;
static const lean_string_object l_Lean_LocalDecl_value___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "dependent let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__4 = (const lean_object*)&l_Lean_LocalDecl_value___closed__4_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__5;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.LocalDecl.setBinderInfo"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__0 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected let declaration"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__1_value;
static lean_once_cell_t l_Lean_LocalDecl_setBinderInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg();
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalContext_mkEmpty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkEmpty___closed__0;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.LocalContext.get!"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown free variable"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__1_value;
static lean_once_cell_t l_Lean_LocalContext_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_getFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_getFVarIds___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFVarIds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.LocalContext.getFromUserName!"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unknown local declaration `"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__1_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__2 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__0 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__1 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_mkBinding___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.LocalContext.mkBinding"};
static const lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__0 = (const lean_object*)&l_Lean_LocalContext_mkBinding___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_LocalContext_mkBinding___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_findFromUserNames___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___redArg___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LocalDeclKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_LocalDeclKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_23_){
_start:
{
lean_inc(v_default_23_);
return v_default_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_24_);
lean_dec(v_default_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_default_29_){
_start:
{
lean_inc(v_default_29_);
return v_default_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_default_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_LocalDeclKind_default_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_default_33_);
lean_dec(v_default_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_36_){
_start:
{
lean_inc(v_implDetail_36_);
return v_implDetail_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_37_);
lean_dec(v_implDetail_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_implDetail_42_){
_start:
{
lean_inc(v_implDetail_42_);
return v_implDetail_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_implDetail_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_implDetail_46_);
lean_dec(v_implDetail_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_49_){
_start:
{
lean_inc(v_auxDecl_49_);
return v_auxDecl_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_50_);
lean_dec(v_auxDecl_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_auxDecl_55_){
_start:
{
lean_inc(v_auxDecl_55_);
return v_auxDecl_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_auxDecl_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_auxDecl_59_);
lean_dec(v_auxDecl_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_94_; 
switch(v_x_77_)
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_78_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_80_ = v___x_102_;
goto v___jp_79_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_80_ = v___x_103_;
goto v___jp_79_;
}
}
case 1:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_78_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_87_ = v___x_106_;
goto v___jp_86_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_87_ = v___x_107_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_78_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_94_ = v___x_111_;
goto v___jp_93_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
uint8_t v_x_171__boxed_114_; lean_object* v_res_115_; 
v_x_171__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_instReprLocalDeclKind_repr(v_x_171__boxed_114_, v_prec_113_);
lean_dec(v_prec_113_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_le(v_n_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_dec_le(v_n_118_, v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_LocalDeclKind_ofNat(v_n_126_);
lean_dec(v_n_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_129_, uint8_t v_y_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_LocalDeclKind_ctorIdx(v_x_129_);
v___x_132_ = l_Lean_LocalDeclKind_ctorIdx(v_y_130_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_x_20__boxed_136_; uint8_t v_y_21__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_20__boxed_136_ = lean_unbox(v_x_134_);
v_y_21__boxed_137_ = lean_unbox(v_y_135_);
v_res_138_ = l_Lean_instDecidableEqLocalDeclKind(v_x_20__boxed_136_, v_y_21__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_140_){
_start:
{
switch(v_x_140_)
{
case 0:
{
uint64_t v___x_141_; 
v___x_141_ = 0ULL;
return v___x_141_;
}
case 1:
{
uint64_t v___x_142_; 
v___x_142_ = 1ULL;
return v___x_142_;
}
default: 
{
uint64_t v___x_143_; 
v___x_143_ = 2ULL;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_40__boxed_145_; uint64_t v_res_146_; lean_object* v_r_147_; 
v_x_40__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object* v_binderName_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Name_isImplementationDetail(v_binderName_150_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 1;
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofBinderName___boxed(lean_object* v_binderName_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_154_);
lean_dec(v_binderName_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(0u);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_unsigned_to_nat(1u);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_LocalDecl_ctorIdx(v_x_160_);
lean_dec_ref(v_x_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_162_, lean_object* v_k_163_){
_start:
{
if (lean_obj_tag(v_t_162_) == 0)
{
lean_object* v_index_164_; lean_object* v_fvarId_165_; lean_object* v_userName_166_; lean_object* v_type_167_; uint8_t v_bi_168_; uint8_t v_kind_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_index_164_ = lean_ctor_get(v_t_162_, 0);
lean_inc(v_index_164_);
v_fvarId_165_ = lean_ctor_get(v_t_162_, 1);
lean_inc(v_fvarId_165_);
v_userName_166_ = lean_ctor_get(v_t_162_, 2);
lean_inc(v_userName_166_);
v_type_167_ = lean_ctor_get(v_t_162_, 3);
lean_inc_ref(v_type_167_);
v_bi_168_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*4);
v_kind_169_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_162_, 4);
v___x_170_ = lean_box(v_bi_168_);
v___x_171_ = lean_box(v_kind_169_);
v___x_172_ = lean_apply_6(v_k_163_, v_index_164_, v_fvarId_165_, v_userName_166_, v_type_167_, v___x_170_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_index_173_; lean_object* v_fvarId_174_; lean_object* v_userName_175_; lean_object* v_type_176_; lean_object* v_value_177_; uint8_t v_nondep_178_; uint8_t v_kind_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_index_173_ = lean_ctor_get(v_t_162_, 0);
lean_inc(v_index_173_);
v_fvarId_174_ = lean_ctor_get(v_t_162_, 1);
lean_inc(v_fvarId_174_);
v_userName_175_ = lean_ctor_get(v_t_162_, 2);
lean_inc(v_userName_175_);
v_type_176_ = lean_ctor_get(v_t_162_, 3);
lean_inc_ref(v_type_176_);
v_value_177_ = lean_ctor_get(v_t_162_, 4);
lean_inc_ref(v_value_177_);
v_nondep_178_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*5);
v_kind_179_ = lean_ctor_get_uint8(v_t_162_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_162_, 5);
v___x_180_ = lean_box(v_nondep_178_);
v___x_181_ = lean_box(v_kind_179_);
v___x_182_ = lean_apply_7(v_k_163_, v_index_173_, v_fvarId_174_, v_userName_175_, v_type_176_, v_value_177_, v___x_180_, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_185_, v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_LocalDecl_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_191_, v_h_192_, v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_195_, lean_object* v_cdecl_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_195_, v_cdecl_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_cdecl_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_199_, v_cdecl_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_203_, lean_object* v_ldecl_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_203_, v_ldecl_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_ldecl_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_207_, v_ldecl_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
v___x_215_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_216_ = l_Lean_Expr_const___override(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = 0;
v___x_218_ = 0;
v___x_219_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_220_ = lean_box(0);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_220_);
lean_ctor_set(v___x_222_, 3, v___x_219_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*4, v___x_218_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*4 + 1, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, uint8_t v_bi_229_){
_start:
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_231_, 0, v_index_225_);
lean_ctor_set(v___x_231_, 1, v_fvarId_226_);
lean_ctor_set(v___x_231_, 2, v_userName_227_);
lean_ctor_set(v___x_231_, 3, v_type_228_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4, v_bi_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4 + 1, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_bi_236_){
_start:
{
uint8_t v_bi_boxed_237_; lean_object* v_res_238_; 
v_bi_boxed_237_ = lean_unbox(v_bi_236_);
v_res_238_ = lean_mk_local_decl(v_index_232_, v_fvarId_233_, v_userName_234_, v_type_235_, v_bi_boxed_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_239_, lean_object* v_fvarId_240_, lean_object* v_userName_241_, lean_object* v_type_242_, lean_object* v_val_243_){
_start:
{
uint8_t v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; 
v___x_244_ = 0;
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_246_, 0, v_index_239_);
lean_ctor_set(v___x_246_, 1, v_fvarId_240_);
lean_ctor_set(v___x_246_, 2, v_userName_241_);
lean_ctor_set(v___x_246_, 3, v_type_242_);
lean_ctor_set(v___x_246_, 4, v_val_243_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*5, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*5 + 1, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
uint8_t v_bi_248_; 
v_bi_248_ = lean_ctor_get_uint8(v_x_247_, sizeof(void*)*4);
lean_dec_ref_known(v_x_247_, 4);
return v_bi_248_;
}
else
{
uint8_t v___x_249_; 
lean_dec_ref(v_x_247_);
v___x_249_ = 0;
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = lean_local_decl_binder_info(v_x_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_253_, uint8_t v_x_254_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
else
{
uint8_t v_nondep_256_; 
v_nondep_256_ = lean_ctor_get_uint8(v_x_253_, sizeof(void*)*5);
if (v_nondep_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
else
{
return v_x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
uint8_t v_x_53__boxed_260_; uint8_t v_res_261_; lean_object* v_r_262_; 
v_x_53__boxed_260_ = lean_unbox(v_x_259_);
v_res_261_ = l_Lean_LocalDecl_isLet(v_x_258_, v_x_53__boxed_260_);
lean_dec_ref(v_x_258_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_263_){
_start:
{
lean_object* v_index_264_; 
v_index_264_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_index_264_);
return v_index_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_LocalDecl_index(v_x_265_);
lean_dec_ref(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v_fvarId_269_; lean_object* v_userName_270_; lean_object* v_type_271_; uint8_t v_bi_272_; uint8_t v_kind_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_fvarId_269_ = lean_ctor_get(v_x_267_, 1);
v_userName_270_ = lean_ctor_get(v_x_267_, 2);
v_type_271_ = lean_ctor_get(v_x_267_, 3);
v_bi_272_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*4);
v_kind_273_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*4 + 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_x_267_, 0);
lean_dec(v_unused_281_);
v___x_275_ = v_x_267_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_type_271_);
lean_inc(v_userName_270_);
lean_inc(v_fvarId_269_);
lean_dec(v_x_267_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_x_268_);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_x_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_fvarId_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_userName_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_type_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*4, v_bi_272_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*4 + 1, v_kind_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v_fvarId_282_; lean_object* v_userName_283_; lean_object* v_type_284_; lean_object* v_value_285_; uint8_t v_nondep_286_; uint8_t v_kind_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_fvarId_282_ = lean_ctor_get(v_x_267_, 1);
v_userName_283_ = lean_ctor_get(v_x_267_, 2);
v_type_284_ = lean_ctor_get(v_x_267_, 3);
v_value_285_ = lean_ctor_get(v_x_267_, 4);
v_nondep_286_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*5);
v_kind_287_ = lean_ctor_get_uint8(v_x_267_, sizeof(void*)*5 + 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_x_267_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v_x_267_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_value_285_);
lean_inc(v_type_284_);
lean_inc(v_userName_283_);
lean_inc(v_fvarId_282_);
lean_dec(v_x_267_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_x_268_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_x_268_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_fvarId_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_userName_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_type_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_value_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*5, v_nondep_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*5 + 1, v_kind_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_296_){
_start:
{
lean_object* v_fvarId_297_; 
v_fvarId_297_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_fvarId_297_);
return v_fvarId_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_LocalDecl_fvarId(v_x_298_);
lean_dec_ref(v_x_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_300_){
_start:
{
lean_object* v_userName_301_; 
v_userName_301_ = lean_ctor_get(v_x_300_, 2);
lean_inc(v_userName_301_);
return v_userName_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_LocalDecl_userName(v_x_302_);
lean_dec_ref(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_304_){
_start:
{
lean_object* v_type_305_; 
v_type_305_ = lean_ctor_get(v_x_304_, 3);
lean_inc_ref(v_type_305_);
return v_type_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_LocalDecl_type(v_x_306_);
lean_dec_ref(v_x_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_index_310_; lean_object* v_fvarId_311_; lean_object* v_userName_312_; uint8_t v_bi_313_; uint8_t v_kind_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_index_310_ = lean_ctor_get(v_x_308_, 0);
v_fvarId_311_ = lean_ctor_get(v_x_308_, 1);
v_userName_312_ = lean_ctor_get(v_x_308_, 2);
v_bi_313_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*4);
v_kind_314_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*4 + 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_x_308_, 3);
lean_dec(v_unused_322_);
v___x_316_ = v_x_308_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_userName_312_);
lean_inc(v_fvarId_311_);
lean_inc(v_index_310_);
lean_dec(v_x_308_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 3, v_x_309_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_index_310_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_fvarId_311_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_userName_312_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_x_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*4, v_bi_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*4 + 1, v_kind_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_index_323_; lean_object* v_fvarId_324_; lean_object* v_userName_325_; lean_object* v_value_326_; uint8_t v_nondep_327_; uint8_t v_kind_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_index_323_ = lean_ctor_get(v_x_308_, 0);
v_fvarId_324_ = lean_ctor_get(v_x_308_, 1);
v_userName_325_ = lean_ctor_get(v_x_308_, 2);
v_value_326_ = lean_ctor_get(v_x_308_, 4);
v_nondep_327_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*5);
v_kind_328_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*5 + 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_x_308_, 3);
lean_dec(v_unused_336_);
v___x_330_ = v_x_308_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_value_326_);
lean_inc(v_userName_325_);
lean_inc(v_fvarId_324_);
lean_inc(v_index_323_);
lean_dec(v_x_308_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 3, v_x_309_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_index_323_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_fvarId_324_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_userName_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_x_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_value_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*5, v_nondep_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*5 + 1, v_kind_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
uint8_t v_bi_338_; 
v_bi_338_ = lean_ctor_get_uint8(v_x_337_, sizeof(void*)*4);
return v_bi_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Lean_LocalDecl_binderInfo(v_x_340_);
lean_dec_ref(v_x_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
uint8_t v_kind_344_; 
v_kind_344_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*4 + 1);
return v_kind_344_;
}
else
{
uint8_t v_kind_345_; 
v_kind_345_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*5 + 1);
return v_kind_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_LocalDecl_kind(v_x_346_);
lean_dec_ref(v_x_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isAuxDecl___closed__0(void){
_start:
{
uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_349_ = 2;
v___x_350_ = l_Lean_LocalDeclKind_ctorIdx(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_351_){
_start:
{
uint8_t v___y_353_; 
if (lean_obj_tag(v_d_351_) == 0)
{
uint8_t v_kind_357_; 
v_kind_357_ = lean_ctor_get_uint8(v_d_351_, sizeof(void*)*4 + 1);
v___y_353_ = v_kind_357_;
goto v___jp_352_;
}
else
{
uint8_t v_kind_358_; 
v_kind_358_ = lean_ctor_get_uint8(v_d_351_, sizeof(void*)*5 + 1);
v___y_353_ = v_kind_358_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = l_Lean_LocalDeclKind_ctorIdx(v___y_353_);
v___x_355_ = lean_obj_once(&l_Lean_LocalDecl_isAuxDecl___closed__0, &l_Lean_LocalDecl_isAuxDecl___closed__0_once, _init_l_Lean_LocalDecl_isAuxDecl___closed__0);
v___x_356_ = lean_nat_dec_eq(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lean_LocalDecl_isAuxDecl(v_d_359_);
lean_dec_ref(v_d_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isImplementationDetail___closed__0(void){
_start:
{
uint8_t v___x_362_; lean_object* v___x_363_; 
v___x_362_ = 0;
v___x_363_ = l_Lean_LocalDeclKind_ctorIdx(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_364_){
_start:
{
uint8_t v___y_366_; 
if (lean_obj_tag(v_d_364_) == 0)
{
uint8_t v_kind_372_; 
v_kind_372_ = lean_ctor_get_uint8(v_d_364_, sizeof(void*)*4 + 1);
v___y_366_ = v_kind_372_;
goto v___jp_365_;
}
else
{
uint8_t v_kind_373_; 
v_kind_373_ = lean_ctor_get_uint8(v_d_364_, sizeof(void*)*5 + 1);
v___y_366_ = v_kind_373_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = l_Lean_LocalDeclKind_ctorIdx(v___y_366_);
v___x_368_ = lean_obj_once(&l_Lean_LocalDecl_isImplementationDetail___closed__0, &l_Lean_LocalDecl_isImplementationDetail___closed__0_once, _init_l_Lean_LocalDecl_isImplementationDetail___closed__0);
v___x_369_ = lean_nat_dec_eq(v___x_367_, v___x_368_);
lean_dec(v___x_367_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
v___x_370_ = 1;
return v___x_370_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_LocalDecl_isImplementationDetail(v_d_374_);
lean_dec_ref(v_d_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_377_, uint8_t v_x_378_){
_start:
{
if (lean_obj_tag(v_x_377_) == 1)
{
uint8_t v_nondep_379_; 
v_nondep_379_ = lean_ctor_get_uint8(v_x_377_, sizeof(void*)*5);
if (v_nondep_379_ == 0)
{
lean_object* v_value_380_; lean_object* v___x_381_; 
v_value_380_ = lean_ctor_get(v_x_377_, 4);
lean_inc_ref(v_value_380_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_value_380_);
return v___x_381_;
}
else
{
if (v_x_378_ == 1)
{
lean_object* v_value_382_; lean_object* v___x_383_; 
v_value_382_ = lean_ctor_get(v_x_377_, 4);
lean_inc_ref(v_value_382_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v_value_382_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint8_t v_x_47__boxed_388_; lean_object* v_res_389_; 
v_x_47__boxed_388_ = lean_unbox(v_x_387_);
v_res_389_ = l_Lean_LocalDecl_value_x3f(v_x_386_, v_x_47__boxed_388_);
lean_dec_ref(v_x_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_instInhabitedExpr;
v___x_392_ = lean_panic_fn_borrowed(v___x_391_, v_msg_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_397_ = lean_unsigned_to_nat(54u);
v___x_398_ = lean_unsigned_to_nat(183u);
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_400_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_404_ = lean_unsigned_to_nat(54u);
v___x_405_ = lean_unsigned_to_nat(186u);
v___x_406_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_407_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_408_ = l_mkPanicMessageWithDecl(v___x_407_, v___x_406_, v___x_405_, v___x_404_, v___x_403_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_409_, uint8_t v_x_410_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_412_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_411_);
return v___x_412_;
}
else
{
uint8_t v_nondep_413_; 
v_nondep_413_ = lean_ctor_get_uint8(v_x_409_, sizeof(void*)*5);
if (v_nondep_413_ == 0)
{
lean_object* v_value_414_; 
v_value_414_ = lean_ctor_get(v_x_409_, 4);
lean_inc_ref(v_value_414_);
return v_value_414_;
}
else
{
if (v_x_410_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_416_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_415_);
return v___x_416_;
}
else
{
lean_object* v_value_417_; 
v_value_417_ = lean_ctor_get(v_x_409_, 4);
lean_inc_ref(v_value_417_);
return v_value_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint8_t v_x_143__boxed_420_; lean_object* v_res_421_; 
v_x_143__boxed_420_ = lean_unbox(v_x_419_);
v_res_421_ = l_Lean_LocalDecl_value(v_x_418_, v_x_143__boxed_420_);
lean_dec_ref(v_x_418_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_422_, uint8_t v_x_423_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
else
{
uint8_t v_nondep_425_; 
v_nondep_425_ = lean_ctor_get_uint8(v_x_422_, sizeof(void*)*5);
if (v_nondep_425_ == 0)
{
uint8_t v___x_426_; 
v___x_426_ = 1;
return v___x_426_;
}
else
{
return v_x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_x_72__boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_x_72__boxed_429_ = lean_unbox(v_x_428_);
v_res_430_ = l_Lean_LocalDecl_hasValue(v_x_427_, v_x_72__boxed_429_);
lean_dec_ref(v_x_427_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_432_) == 1)
{
lean_object* v_index_434_; lean_object* v_fvarId_435_; lean_object* v_userName_436_; lean_object* v_type_437_; uint8_t v_nondep_438_; uint8_t v_kind_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_index_434_ = lean_ctor_get(v_x_432_, 0);
v_fvarId_435_ = lean_ctor_get(v_x_432_, 1);
v_userName_436_ = lean_ctor_get(v_x_432_, 2);
v_type_437_ = lean_ctor_get(v_x_432_, 3);
v_nondep_438_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*5);
v_kind_439_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*5 + 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_x_432_, 4);
lean_dec(v_unused_447_);
v___x_441_ = v_x_432_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_type_437_);
lean_inc(v_userName_436_);
lean_inc(v_fvarId_435_);
lean_inc(v_index_434_);
lean_dec(v_x_432_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 4, v_x_433_);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_index_434_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_fvarId_435_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_userName_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_type_437_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_x_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*5, v_nondep_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*5 + 1, v_kind_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_dec_ref(v_x_433_);
return v_x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_448_, uint8_t v_x_449_){
_start:
{
if (lean_obj_tag(v_x_448_) == 1)
{
lean_object* v_index_450_; lean_object* v_fvarId_451_; lean_object* v_userName_452_; lean_object* v_type_453_; lean_object* v_value_454_; uint8_t v_kind_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_index_450_ = lean_ctor_get(v_x_448_, 0);
v_fvarId_451_ = lean_ctor_get(v_x_448_, 1);
v_userName_452_ = lean_ctor_get(v_x_448_, 2);
v_type_453_ = lean_ctor_get(v_x_448_, 3);
v_value_454_ = lean_ctor_get(v_x_448_, 4);
v_kind_455_ = lean_ctor_get_uint8(v_x_448_, sizeof(void*)*5 + 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v_x_448_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_value_454_);
lean_inc(v_type_453_);
lean_inc(v_userName_452_);
lean_inc(v_fvarId_451_);
lean_inc(v_index_450_);
lean_dec(v_x_448_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_index_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_fvarId_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_userName_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_type_453_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_value_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_461_, sizeof(void*)*5 + 1, v_kind_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*5, v_x_449_);
return v___x_460_;
}
}
}
else
{
return v_x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_x_23__boxed_465_; lean_object* v_res_466_; 
v_x_23__boxed_465_ = lean_unbox(v_x_464_);
v_res_466_ = l_Lean_LocalDecl_setNondep(v_x_463_, v_x_23__boxed_465_);
return v_res_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 1)
{
uint8_t v_nondep_468_; 
v_nondep_468_ = lean_ctor_get_uint8(v_x_467_, sizeof(void*)*5);
return v_nondep_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_470_){
_start:
{
uint8_t v_res_471_; lean_object* v_r_472_; 
v_res_471_ = l_Lean_LocalDecl_isNondep(v_x_470_);
lean_dec_ref(v_x_470_);
v_r_472_ = lean_box(v_res_471_);
return v_r_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v_index_475_; lean_object* v_fvarId_476_; lean_object* v_type_477_; uint8_t v_bi_478_; uint8_t v_kind_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_index_475_ = lean_ctor_get(v_x_473_, 0);
v_fvarId_476_ = lean_ctor_get(v_x_473_, 1);
v_type_477_ = lean_ctor_get(v_x_473_, 3);
v_bi_478_ = lean_ctor_get_uint8(v_x_473_, sizeof(void*)*4);
v_kind_479_ = lean_ctor_get_uint8(v_x_473_, sizeof(void*)*4 + 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_473_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_x_473_, 2);
lean_dec(v_unused_487_);
v___x_481_ = v_x_473_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_type_477_);
lean_inc(v_fvarId_476_);
lean_inc(v_index_475_);
lean_dec(v_x_473_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 2, v_x_474_);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_index_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_fvarId_476_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_x_474_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_type_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*4, v_bi_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*4 + 1, v_kind_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_index_488_; lean_object* v_fvarId_489_; lean_object* v_type_490_; lean_object* v_value_491_; uint8_t v_nondep_492_; uint8_t v_kind_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_index_488_ = lean_ctor_get(v_x_473_, 0);
v_fvarId_489_ = lean_ctor_get(v_x_473_, 1);
v_type_490_ = lean_ctor_get(v_x_473_, 3);
v_value_491_ = lean_ctor_get(v_x_473_, 4);
v_nondep_492_ = lean_ctor_get_uint8(v_x_473_, sizeof(void*)*5);
v_kind_493_ = lean_ctor_get_uint8(v_x_473_, sizeof(void*)*5 + 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_x_473_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_x_473_, 2);
lean_dec(v_unused_501_);
v___x_495_ = v_x_473_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_value_491_);
lean_inc(v_type_490_);
lean_inc(v_fvarId_489_);
lean_inc(v_index_488_);
lean_dec(v_x_473_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 2, v_x_474_);
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_index_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_fvarId_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_x_474_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_type_490_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_value_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*5, v_nondep_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*5 + 1, v_kind_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = l_Lean_instInhabitedLocalDecl_default;
v___x_504_ = lean_panic_fn_borrowed(v___x_503_, v_msg_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_507_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_508_ = lean_unsigned_to_nat(38u);
v___x_509_ = lean_unsigned_to_nat(248u);
v___x_510_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_511_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_512_ = l_mkPanicMessageWithDecl(v___x_511_, v___x_510_, v___x_509_, v___x_508_, v___x_507_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_513_, uint8_t v_x_514_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v_index_515_; lean_object* v_fvarId_516_; lean_object* v_userName_517_; lean_object* v_type_518_; uint8_t v_kind_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_index_515_ = lean_ctor_get(v_x_513_, 0);
v_fvarId_516_ = lean_ctor_get(v_x_513_, 1);
v_userName_517_ = lean_ctor_get(v_x_513_, 2);
v_type_518_ = lean_ctor_get(v_x_513_, 3);
v_kind_519_ = lean_ctor_get_uint8(v_x_513_, sizeof(void*)*4 + 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v_x_513_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_type_518_);
lean_inc(v_userName_517_);
lean_inc(v_fvarId_516_);
lean_inc(v_index_515_);
lean_dec(v_x_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_index_515_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_fvarId_516_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_userName_517_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_type_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*4 + 1, v_kind_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*4, v_x_514_);
return v___x_524_;
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v_x_513_, 5);
v___x_527_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_528_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_527_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_x_84__boxed_531_; lean_object* v_res_532_; 
v_x_84__boxed_531_ = lean_unbox(v_x_530_);
v_res_532_ = l_Lean_LocalDecl_setBinderInfo(v_x_529_, v_x_84__boxed_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_533_){
_start:
{
lean_object* v_fvarId_534_; lean_object* v___x_535_; 
v_fvarId_534_ = lean_ctor_get(v_decl_533_, 1);
lean_inc(v_fvarId_534_);
lean_dec_ref(v_decl_533_);
v___x_535_ = l_Lean_mkFVar(v_fvarId_534_);
return v___x_535_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_type_537_; uint8_t v___x_538_; 
v_type_537_ = lean_ctor_get(v_x_536_, 3);
v___x_538_ = l_Lean_Expr_hasExprMVar(v_type_537_);
return v___x_538_;
}
else
{
lean_object* v_type_539_; lean_object* v_value_540_; uint8_t v___x_541_; 
v_type_539_ = lean_ctor_get(v_x_536_, 3);
v_value_540_ = lean_ctor_get(v_x_536_, 4);
v___x_541_ = l_Lean_Expr_hasExprMVar(v_type_539_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Expr_hasExprMVar(v_value_540_);
return v___x_542_;
}
else
{
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l_Lean_LocalDecl_hasExprMVar(v_x_543_);
lean_dec_ref(v_x_543_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_546_, uint8_t v_x_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_object* v_index_548_; lean_object* v_fvarId_549_; lean_object* v_userName_550_; lean_object* v_type_551_; uint8_t v_bi_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_index_548_ = lean_ctor_get(v_x_546_, 0);
v_fvarId_549_ = lean_ctor_get(v_x_546_, 1);
v_userName_550_ = lean_ctor_get(v_x_546_, 2);
v_type_551_ = lean_ctor_get(v_x_546_, 3);
v_bi_552_ = lean_ctor_get_uint8(v_x_546_, sizeof(void*)*4);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v_x_546_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_type_551_);
lean_inc(v_userName_550_);
lean_inc(v_fvarId_549_);
lean_inc(v_index_548_);
lean_dec(v_x_546_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_index_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_fvarId_549_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_userName_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_type_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*4, v_bi_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*4 + 1, v_x_547_);
return v___x_557_;
}
}
}
else
{
lean_object* v_index_560_; lean_object* v_fvarId_561_; lean_object* v_userName_562_; lean_object* v_type_563_; lean_object* v_value_564_; uint8_t v_nondep_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_index_560_ = lean_ctor_get(v_x_546_, 0);
v_fvarId_561_ = lean_ctor_get(v_x_546_, 1);
v_userName_562_ = lean_ctor_get(v_x_546_, 2);
v_type_563_ = lean_ctor_get(v_x_546_, 3);
v_value_564_ = lean_ctor_get(v_x_546_, 4);
v_nondep_565_ = lean_ctor_get_uint8(v_x_546_, sizeof(void*)*5);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v_x_546_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_value_564_);
lean_inc(v_type_563_);
lean_inc(v_userName_562_);
lean_inc(v_fvarId_561_);
lean_inc(v_index_560_);
lean_dec(v_x_546_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_index_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_fvarId_561_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_userName_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_type_563_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_value_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*5, v_nondep_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*5 + 1, v_x_547_);
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
uint8_t v_x_31__boxed_575_; lean_object* v_res_576_; 
v_x_31__boxed_575_ = lean_unbox(v_x_574_);
v_res_576_ = l_Lean_LocalDecl_setKind(v_x_573_, v_x_31__boxed_575_);
return v_res_576_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_577_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(32u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_583_ = ((size_t)5ULL);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_unsigned_to_nat(32u);
v___x_586_ = lean_mk_empty_array_with_capacity(v___x_585_);
v___x_587_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_588_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_584_);
lean_ctor_set(v___x_588_, 3, v___x_584_);
lean_ctor_set_usize(v___x_588_, 4, v___x_583_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_box(1);
v___x_590_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_589_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_instInhabitedLocalContext_default;
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg(){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(32u);
v___x_597_ = lean_mk_empty_array_with_capacity(v___x_596_);
lean_dec_ref(v___x_597_);
v___x_598_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object* v___dummy_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_LocalContext_mkEmpty___redArg();
return v_res_600_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_LocalContext_mkEmpty___redArg();
return v___x_601_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(32u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
lean_dec_ref(v___x_605_);
v___x_606_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_609_);
lean_dec_ref(v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_x_613_){
_start:
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_615_, lean_object* v_x_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_615_, v_x_616_);
lean_dec_ref(v_x_616_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object* v_lctx_619_){
_start:
{
lean_object* v_fvarIdToDecl_620_; uint8_t v___x_621_; 
v_fvarIdToDecl_620_ = lean_ctor_get(v_lctx_619_, 0);
v___x_621_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Lean_LocalContext_isEmpty(v_lctx_622_);
lean_dec_ref(v_lctx_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_ks_629_; lean_object* v_vs_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_654_; 
v_ks_629_ = lean_ctor_get(v_x_625_, 0);
v_vs_630_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_654_ == 0)
{
v___x_632_ = v_x_625_;
v_isShared_633_ = v_isSharedCheck_654_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_vs_630_);
lean_inc(v_ks_629_);
lean_dec(v_x_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_654_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_ks_629_);
v___x_635_ = lean_nat_dec_lt(v_x_626_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
lean_dec(v_x_626_);
v___x_636_ = lean_array_push(v_ks_629_, v_x_627_);
v___x_637_ = lean_array_push(v_vs_630_, v_x_628_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_637_);
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_639_ = v___x_632_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v_k_x27_641_; uint8_t v___x_642_; 
v_k_x27_641_ = lean_array_fget_borrowed(v_ks_629_, v_x_626_);
v___x_642_ = l_Lean_instBEqFVarId_beq(v_x_627_, v_k_x27_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_644_; 
if (v_isShared_633_ == 0)
{
v___x_644_ = v___x_632_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_ks_629_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_vs_630_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v_x_626_, v___x_645_);
lean_dec(v_x_626_);
v_x_625_ = v___x_644_;
v_x_626_ = v___x_646_;
goto _start;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = lean_array_fset(v_ks_629_, v_x_626_, v_x_627_);
v___x_650_ = lean_array_fset(v_vs_630_, v_x_626_, v_x_628_);
lean_dec(v_x_626_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_650_);
lean_ctor_set(v___x_632_, 0, v___x_649_);
v___x_652_ = v___x_632_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_655_, v___x_658_, v_k_656_, v_v_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_661_, size_t v_x_662_, size_t v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v_es_666_; size_t v___x_667_; size_t v___x_668_; lean_object* v_j_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_es_666_ = lean_ctor_get(v_x_661_, 0);
v___x_667_ = ((size_t)31ULL);
v___x_668_ = lean_usize_land(v_x_662_, v___x_667_);
v_j_669_ = lean_usize_to_nat(v___x_668_);
v___x_670_ = lean_array_get_size(v_es_666_);
v___x_671_ = lean_nat_dec_lt(v_j_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_j_669_);
lean_dec(v_x_665_);
lean_dec(v_x_664_);
return v_x_661_;
}
else
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_710_; 
lean_inc_ref(v_es_666_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_x_661_, 0);
lean_dec(v_unused_711_);
v___x_673_ = v_x_661_;
v_isShared_674_ = v_isSharedCheck_710_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_x_661_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_710_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_v_675_; lean_object* v___x_676_; lean_object* v_xs_x27_677_; lean_object* v___y_679_; 
v_v_675_ = lean_array_fget(v_es_666_, v_j_669_);
v___x_676_ = lean_box(0);
v_xs_x27_677_ = lean_array_fset(v_es_666_, v_j_669_, v___x_676_);
switch(lean_obj_tag(v_v_675_))
{
case 0:
{
lean_object* v_key_684_; lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v_key_684_ = lean_ctor_get(v_v_675_, 0);
v_val_685_ = lean_ctor_get(v_v_675_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_v_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v_v_675_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_inc(v_key_684_);
lean_dec(v_v_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_instBEqFVarId_beq(v_x_664_, v_key_684_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_del_object(v___x_687_);
v___x_690_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_684_, v_val_685_, v_x_664_, v_x_665_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___y_679_ = v___x_691_;
goto v___jp_678_;
}
else
{
lean_object* v___x_693_; 
lean_dec(v_val_685_);
lean_dec(v_key_684_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_x_665_);
lean_ctor_set(v___x_687_, 0, v_x_664_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_x_664_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_x_665_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v___y_679_ = v___x_693_;
goto v___jp_678_;
}
}
}
}
case 1:
{
lean_object* v_node_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v_node_696_ = lean_ctor_get(v_v_675_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_v_675_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v_v_675_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_node_696_);
lean_dec(v_v_675_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_usize_shift_right(v_x_662_, v___x_700_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_x_663_, v___x_702_);
v___x_704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_696_, v___x_701_, v___x_703_, v_x_664_, v_x_665_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_704_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v___y_679_ = v___x_706_;
goto v___jp_678_;
}
}
}
default: 
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_x_664_);
lean_ctor_set(v___x_709_, 1, v_x_665_);
v___y_679_ = v___x_709_;
goto v___jp_678_;
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_array_fset(v_xs_x27_677_, v_j_669_, v___y_679_);
lean_dec(v_j_669_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_680_);
v___x_682_ = v___x_673_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
else
{
lean_object* v_ks_712_; lean_object* v_vs_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_731_; 
v_ks_712_ = lean_ctor_get(v_x_661_, 0);
v_vs_713_ = lean_ctor_get(v_x_661_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_731_ == 0)
{
v___x_715_ = v_x_661_;
v_isShared_716_ = v_isSharedCheck_731_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_vs_713_);
lean_inc(v_ks_712_);
lean_dec(v_x_661_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_731_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_ks_712_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_vs_713_);
v___x_718_ = v_reuseFailAlloc_730_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v_newNode_719_; size_t v___x_720_; uint8_t v___x_721_; 
v_newNode_719_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_718_, v_x_664_, v_x_665_);
v___x_720_ = ((size_t)7ULL);
v___x_721_ = lean_usize_dec_le(v___x_720_, v_x_663_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_719_);
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v_ks_725_; lean_object* v_vs_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_ks_725_ = lean_ctor_get(v_newNode_719_, 0);
lean_inc_ref(v_ks_725_);
v_vs_726_ = lean_ctor_get(v_newNode_719_, 1);
lean_inc_ref(v_vs_726_);
lean_dec_ref(v_newNode_719_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_663_, v_ks_725_, v_vs_726_, v___x_727_, v___x_728_);
lean_dec_ref(v_vs_726_);
lean_dec_ref(v_ks_725_);
return v___x_729_;
}
else
{
return v_newNode_719_;
}
}
else
{
return v_newNode_719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_732_, lean_object* v_keys_733_, lean_object* v_vals_734_, lean_object* v_i_735_, lean_object* v_entries_736_){
_start:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_array_get_size(v_keys_733_);
v___x_738_ = lean_nat_dec_lt(v_i_735_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v_i_735_);
return v_entries_736_;
}
else
{
lean_object* v_k_739_; lean_object* v_v_740_; uint64_t v___x_741_; size_t v_h_742_; size_t v___x_743_; lean_object* v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v_h_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_k_739_ = lean_array_fget_borrowed(v_keys_733_, v_i_735_);
v_v_740_ = lean_array_fget_borrowed(v_vals_734_, v_i_735_);
v___x_741_ = l_Lean_instHashableFVarId_hash(v_k_739_);
v_h_742_ = lean_uint64_to_usize(v___x_741_);
v___x_743_ = ((size_t)5ULL);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = ((size_t)1ULL);
v___x_746_ = lean_usize_sub(v_depth_732_, v___x_745_);
v___x_747_ = lean_usize_mul(v___x_743_, v___x_746_);
v_h_748_ = lean_usize_shift_right(v_h_742_, v___x_747_);
v___x_749_ = lean_nat_add(v_i_735_, v___x_744_);
lean_dec(v_i_735_);
lean_inc(v_v_740_);
lean_inc(v_k_739_);
v___x_750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_736_, v_h_748_, v_depth_732_, v_k_739_, v_v_740_);
v_i_735_ = v___x_749_;
v_entries_736_ = v___x_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_i_755_, lean_object* v_entries_756_){
_start:
{
size_t v_depth_boxed_757_; lean_object* v_res_758_; 
v_depth_boxed_757_ = lean_unbox_usize(v_depth_752_);
lean_dec(v_depth_752_);
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_757_, v_keys_753_, v_vals_754_, v_i_755_, v_entries_756_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_365__boxed_764_; size_t v_x_366__boxed_765_; lean_object* v_res_766_; 
v_x_365__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_x_366__boxed_765_ = lean_unbox_usize(v_x_761_);
lean_dec(v_x_761_);
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_759_, v_x_365__boxed_764_, v_x_366__boxed_765_, v_x_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
uint64_t v___x_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_770_ = l_Lean_instHashableFVarId_hash(v_x_768_);
v___x_771_ = lean_uint64_to_usize(v___x_770_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_767_, v___x_771_, v___x_772_, v_x_768_, v_x_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_774_, lean_object* v_fvarId_775_, lean_object* v_userName_776_, lean_object* v_type_777_, uint8_t v_bi_778_, uint8_t v_kind_779_){
_start:
{
lean_object* v_decls_780_; lean_object* v_fvarIdToDecl_781_; lean_object* v_auxDeclToFullName_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_794_; 
v_decls_780_ = lean_ctor_get(v_lctx_774_, 1);
v_fvarIdToDecl_781_ = lean_ctor_get(v_lctx_774_, 0);
v_auxDeclToFullName_782_ = lean_ctor_get(v_lctx_774_, 2);
v_isSharedCheck_794_ = !lean_is_exclusive(v_lctx_774_);
if (v_isSharedCheck_794_ == 0)
{
v___x_784_ = v_lctx_774_;
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_auxDeclToFullName_782_);
lean_inc(v_decls_780_);
lean_inc(v_fvarIdToDecl_781_);
lean_dec(v_lctx_774_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_size_786_; lean_object* v_decl_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_size_786_ = lean_ctor_get(v_decls_780_, 2);
lean_inc(v_fvarId_775_);
lean_inc(v_size_786_);
v_decl_787_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_787_, 0, v_size_786_);
lean_ctor_set(v_decl_787_, 1, v_fvarId_775_);
lean_ctor_set(v_decl_787_, 2, v_userName_776_);
lean_ctor_set(v_decl_787_, 3, v_type_777_);
lean_ctor_set_uint8(v_decl_787_, sizeof(void*)*4, v_bi_778_);
lean_ctor_set_uint8(v_decl_787_, sizeof(void*)*4 + 1, v_kind_779_);
lean_inc_ref(v_decl_787_);
v___x_788_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_781_, v_fvarId_775_, v_decl_787_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_decl_787_);
v___x_790_ = l_Lean_PersistentArray_push___redArg(v_decls_780_, v___x_789_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_790_);
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_auxDeclToFullName_782_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_795_, lean_object* v_fvarId_796_, lean_object* v_userName_797_, lean_object* v_type_798_, lean_object* v_bi_799_, lean_object* v_kind_800_){
_start:
{
uint8_t v_bi_boxed_801_; uint8_t v_kind_boxed_802_; lean_object* v_res_803_; 
v_bi_boxed_801_ = lean_unbox(v_bi_799_);
v_kind_boxed_802_ = lean_unbox(v_kind_800_);
v_res_803_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_795_, v_fvarId_796_, v_userName_797_, v_type_798_, v_bi_boxed_801_, v_kind_boxed_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, size_t v_x_811_, size_t v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_810_, v_x_811_, v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
size_t v_x_565__boxed_822_; size_t v_x_566__boxed_823_; lean_object* v_res_824_; 
v_x_565__boxed_822_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_x_566__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_res_824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_816_, v_x_817_, v_x_565__boxed_822_, v_x_566__boxed_823_, v_x_820_, v_x_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_825_, lean_object* v_n_826_, lean_object* v_k_827_, lean_object* v_v_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_826_, v_k_827_, v_v_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_830_, size_t v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_heq_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_831_, v_keys_832_, v_vals_833_, v_i_835_, v_entries_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_838_, lean_object* v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
size_t v_depth_boxed_845_; lean_object* v_res_846_; 
v_depth_boxed_845_ = lean_unbox_usize(v_depth_839_);
lean_dec(v_depth_839_);
v_res_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_838_, v_depth_boxed_845_, v_keys_840_, v_vals_841_, v_heq_842_, v_i_843_, v_entries_844_);
lean_dec_ref(v_vals_841_);
lean_dec_ref(v_keys_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_848_, v_x_849_, v_x_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_853_, lean_object* v_fvarId_854_, lean_object* v_userName_855_, lean_object* v_type_856_, uint8_t v_bi_857_){
_start:
{
uint8_t v___x_858_; lean_object* v___x_859_; 
v___x_858_ = 0;
v___x_859_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_853_, v_fvarId_854_, v_userName_855_, v_type_856_, v_bi_857_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_860_, lean_object* v_fvarId_861_, lean_object* v_userName_862_, lean_object* v_type_863_, lean_object* v_bi_864_){
_start:
{
uint8_t v_bi_boxed_865_; lean_object* v_res_866_; 
v_bi_boxed_865_ = lean_unbox(v_bi_864_);
v_res_866_ = lean_local_ctx_mk_local_decl(v_lctx_860_, v_fvarId_861_, v_userName_862_, v_type_863_, v_bi_boxed_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_867_, lean_object* v_fvarId_868_, lean_object* v_userName_869_, lean_object* v_type_870_, lean_object* v_value_871_, uint8_t v_nondep_872_, uint8_t v_kind_873_){
_start:
{
lean_object* v_decls_874_; lean_object* v_fvarIdToDecl_875_; lean_object* v_auxDeclToFullName_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_888_; 
v_decls_874_ = lean_ctor_get(v_lctx_867_, 1);
v_fvarIdToDecl_875_ = lean_ctor_get(v_lctx_867_, 0);
v_auxDeclToFullName_876_ = lean_ctor_get(v_lctx_867_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_lctx_867_);
if (v_isSharedCheck_888_ == 0)
{
v___x_878_ = v_lctx_867_;
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_auxDeclToFullName_876_);
lean_inc(v_decls_874_);
lean_inc(v_fvarIdToDecl_875_);
lean_dec(v_lctx_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_size_880_; lean_object* v_decl_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_size_880_ = lean_ctor_get(v_decls_874_, 2);
lean_inc(v_fvarId_868_);
lean_inc(v_size_880_);
v_decl_881_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_881_, 0, v_size_880_);
lean_ctor_set(v_decl_881_, 1, v_fvarId_868_);
lean_ctor_set(v_decl_881_, 2, v_userName_869_);
lean_ctor_set(v_decl_881_, 3, v_type_870_);
lean_ctor_set(v_decl_881_, 4, v_value_871_);
lean_ctor_set_uint8(v_decl_881_, sizeof(void*)*5, v_nondep_872_);
lean_ctor_set_uint8(v_decl_881_, sizeof(void*)*5 + 1, v_kind_873_);
lean_inc_ref(v_decl_881_);
v___x_882_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_875_, v_fvarId_868_, v_decl_881_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_decl_881_);
v___x_884_ = l_Lean_PersistentArray_push___redArg(v_decls_874_, v___x_883_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v___x_884_);
lean_ctor_set(v___x_878_, 0, v___x_882_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_auxDeclToFullName_876_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_889_, lean_object* v_fvarId_890_, lean_object* v_userName_891_, lean_object* v_type_892_, lean_object* v_value_893_, lean_object* v_nondep_894_, lean_object* v_kind_895_){
_start:
{
uint8_t v_nondep_boxed_896_; uint8_t v_kind_boxed_897_; lean_object* v_res_898_; 
v_nondep_boxed_896_ = lean_unbox(v_nondep_894_);
v_kind_boxed_897_ = lean_unbox(v_kind_895_);
v_res_898_ = l_Lean_LocalContext_mkLetDecl(v_lctx_889_, v_fvarId_890_, v_userName_891_, v_type_892_, v_value_893_, v_nondep_boxed_896_, v_kind_boxed_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_899_, lean_object* v_fvarId_900_, lean_object* v_userName_901_, lean_object* v_type_902_, lean_object* v_value_903_, uint8_t v_nondep_904_){
_start:
{
uint8_t v___x_905_; lean_object* v___x_906_; 
v___x_905_ = 0;
v___x_906_ = l_Lean_LocalContext_mkLetDecl(v_lctx_899_, v_fvarId_900_, v_userName_901_, v_type_902_, v_value_903_, v_nondep_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_907_, lean_object* v_fvarId_908_, lean_object* v_userName_909_, lean_object* v_type_910_, lean_object* v_value_911_, lean_object* v_nondep_912_){
_start:
{
uint8_t v_nondep_boxed_913_; lean_object* v_res_914_; 
v_nondep_boxed_913_ = lean_unbox(v_nondep_912_);
v_res_914_ = lean_local_ctx_mk_let_decl(v_lctx_907_, v_fvarId_908_, v_userName_909_, v_type_910_, v_value_911_, v_nondep_boxed_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_915_, lean_object* v_fvarId_916_, lean_object* v_userName_917_, lean_object* v_type_918_, lean_object* v_fullName_919_){
_start:
{
lean_object* v_decls_920_; lean_object* v_fvarIdToDecl_921_; lean_object* v_auxDeclToFullName_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_937_; 
v_decls_920_ = lean_ctor_get(v_lctx_915_, 1);
v_fvarIdToDecl_921_ = lean_ctor_get(v_lctx_915_, 0);
v_auxDeclToFullName_922_ = lean_ctor_get(v_lctx_915_, 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v_lctx_915_);
if (v_isSharedCheck_937_ == 0)
{
v___x_924_ = v_lctx_915_;
v_isShared_925_ = v_isSharedCheck_937_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_auxDeclToFullName_922_);
lean_inc(v_decls_920_);
lean_inc(v_fvarIdToDecl_921_);
lean_dec(v_lctx_915_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_937_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_size_926_; uint8_t v___x_927_; uint8_t v___x_928_; lean_object* v_decl_929_; lean_object* v_auxDeclToFullName_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v_size_926_ = lean_ctor_get(v_decls_920_, 2);
v___x_927_ = 0;
v___x_928_ = 2;
lean_inc_n(v_fvarId_916_, 2);
lean_inc(v_size_926_);
v_decl_929_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_929_, 0, v_size_926_);
lean_ctor_set(v_decl_929_, 1, v_fvarId_916_);
lean_ctor_set(v_decl_929_, 2, v_userName_917_);
lean_ctor_set(v_decl_929_, 3, v_type_918_);
lean_ctor_set_uint8(v_decl_929_, sizeof(void*)*4, v___x_927_);
lean_ctor_set_uint8(v_decl_929_, sizeof(void*)*4 + 1, v___x_928_);
v_auxDeclToFullName_930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_916_, v_fullName_919_, v_auxDeclToFullName_922_);
lean_inc_ref(v_decl_929_);
v___x_931_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_921_, v_fvarId_916_, v_decl_929_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v_decl_929_);
v___x_933_ = l_Lean_PersistentArray_push___redArg(v_decls_920_, v___x_932_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 2, v_auxDeclToFullName_930_);
lean_ctor_set(v___x_924_, 1, v___x_933_);
lean_ctor_set(v___x_924_, 0, v___x_931_);
v___x_935_ = v___x_924_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_auxDeclToFullName_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_938_, lean_object* v_newDecl_939_){
_start:
{
lean_object* v_decls_940_; lean_object* v_fvarIdToDecl_941_; lean_object* v_auxDeclToFullName_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_957_; 
v_decls_940_ = lean_ctor_get(v_lctx_938_, 1);
v_fvarIdToDecl_941_ = lean_ctor_get(v_lctx_938_, 0);
v_auxDeclToFullName_942_ = lean_ctor_get(v_lctx_938_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_lctx_938_);
if (v_isSharedCheck_957_ == 0)
{
v___x_944_ = v_lctx_938_;
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_auxDeclToFullName_942_);
lean_inc(v_decls_940_);
lean_inc(v_fvarIdToDecl_941_);
lean_dec(v_lctx_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_size_946_; lean_object* v_newDecl_947_; lean_object* v___y_949_; lean_object* v_fvarId_956_; 
v_size_946_ = lean_ctor_get(v_decls_940_, 2);
lean_inc(v_size_946_);
v_newDecl_947_ = l_Lean_LocalDecl_setIndex(v_newDecl_939_, v_size_946_);
v_fvarId_956_ = lean_ctor_get(v_newDecl_947_, 1);
lean_inc(v_fvarId_956_);
v___y_949_ = v_fvarId_956_;
goto v___jp_948_;
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_inc_ref(v_newDecl_947_);
v___x_950_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_941_, v___y_949_, v_newDecl_947_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_newDecl_947_);
v___x_952_ = l_Lean_PersistentArray_push___redArg(v_decls_940_, v___x_951_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_952_);
lean_ctor_set(v___x_944_, 0, v___x_950_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_auxDeclToFullName_942_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_array_get_size(v_keys_958_);
v___x_963_ = lean_nat_dec_lt(v_i_960_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v_i_960_);
v___x_964_ = lean_box(0);
return v___x_964_;
}
else
{
lean_object* v_k_x27_965_; uint8_t v___x_966_; 
v_k_x27_965_ = lean_array_fget_borrowed(v_keys_958_, v_i_960_);
v___x_966_ = l_Lean_instBEqFVarId_beq(v_k_961_, v_k_x27_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_i_960_, v___x_967_);
lean_dec(v_i_960_);
v_i_960_ = v___x_968_;
goto _start;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_array_fget_borrowed(v_vals_959_, v_i_960_);
lean_dec(v_i_960_);
lean_inc(v___x_970_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_i_974_, lean_object* v_k_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_972_, v_vals_973_, v_i_974_, v_k_975_);
lean_dec(v_k_975_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_977_, size_t v_x_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_977_) == 0)
{
lean_object* v_es_980_; lean_object* v___x_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v_j_984_; lean_object* v___x_985_; 
v_es_980_ = lean_ctor_get(v_x_977_, 0);
v___x_981_ = lean_box(2);
v___x_982_ = ((size_t)31ULL);
v___x_983_ = lean_usize_land(v_x_978_, v___x_982_);
v_j_984_ = lean_usize_to_nat(v___x_983_);
v___x_985_ = lean_array_get_borrowed(v___x_981_, v_es_980_, v_j_984_);
lean_dec(v_j_984_);
switch(lean_obj_tag(v___x_985_))
{
case 0:
{
lean_object* v_key_986_; lean_object* v_val_987_; uint8_t v___x_988_; 
v_key_986_ = lean_ctor_get(v___x_985_, 0);
v_val_987_ = lean_ctor_get(v___x_985_, 1);
v___x_988_ = l_Lean_instBEqFVarId_beq(v_x_979_, v_key_986_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_val_987_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_val_987_);
return v___x_990_;
}
}
case 1:
{
lean_object* v_node_991_; size_t v___x_992_; size_t v___x_993_; 
v_node_991_ = lean_ctor_get(v___x_985_, 0);
v___x_992_ = ((size_t)5ULL);
v___x_993_ = lean_usize_shift_right(v_x_978_, v___x_992_);
v_x_977_ = v_node_991_;
v_x_978_ = v___x_993_;
goto _start;
}
default: 
{
lean_object* v___x_995_; 
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
else
{
lean_object* v_ks_996_; lean_object* v_vs_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_ks_996_ = lean_ctor_get(v_x_977_, 0);
v_vs_997_ = lean_ctor_get(v_x_977_, 1);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_996_, v_vs_997_, v___x_998_, v_x_979_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
size_t v_x_135__boxed_1003_; lean_object* v_res_1004_; 
v_x_135__boxed_1003_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_res_1004_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1000_, v_x_135__boxed_1003_, v_x_1002_);
lean_dec(v_x_1002_);
lean_dec_ref(v_x_1000_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
uint64_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = l_Lean_instHashableFVarId_hash(v_x_1006_);
v___x_1008_ = lean_uint64_to_usize(v___x_1007_);
v___x_1009_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1005_, v___x_1008_, v_x_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1010_, v_x_1011_);
lean_dec(v_x_1011_);
lean_dec_ref(v_x_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1013_, lean_object* v_fvarId_1014_){
_start:
{
lean_object* v_fvarIdToDecl_1015_; lean_object* v___x_1016_; 
v_fvarIdToDecl_1015_ = lean_ctor_get(v_lctx_1013_, 0);
lean_inc_ref(v_fvarIdToDecl_1015_);
lean_dec_ref(v_lctx_1013_);
v___x_1016_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1015_, v_fvarId_1014_);
lean_dec(v_fvarId_1014_);
lean_dec_ref(v_fvarIdToDecl_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1021_, v_x_1022_, v_x_1023_);
lean_dec(v_x_1023_);
lean_dec_ref(v_x_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, size_t v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1026_, v_x_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
size_t v_x_204__boxed_1034_; lean_object* v_res_1035_; 
v_x_204__boxed_1034_ = lean_unbox_usize(v_x_1032_);
lean_dec(v_x_1032_);
v_res_1035_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1030_, v_x_1031_, v_x_204__boxed_1034_, v_x_1033_);
lean_dec(v_x_1033_);
lean_dec_ref(v_x_1031_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1037_, v_vals_1038_, v_i_1040_, v_k_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_heq_1046_, lean_object* v_i_1047_, lean_object* v_k_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1043_, v_keys_1044_, v_vals_1045_, v_heq_1046_, v_i_1047_, v_k_1048_);
lean_dec(v_k_1048_);
lean_dec_ref(v_vals_1045_);
lean_dec_ref(v_keys_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1050_, lean_object* v_e_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = l_Lean_Expr_fvarId_x21(v_e_1051_);
v___x_1053_ = lean_local_ctx_find(v_lctx_1050_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1054_, lean_object* v_e_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1054_, v_e_1055_);
lean_dec_ref(v_e_1055_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1059_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1060_ = lean_unsigned_to_nat(14u);
v___x_1061_ = lean_unsigned_to_nat(350u);
v___x_1062_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1063_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1064_ = l_mkPanicMessageWithDecl(v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_, v___x_1059_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1065_, lean_object* v_fvarId_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_local_ctx_find(v_lctx_1065_, v_fvarId_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1069_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v_val_1070_; 
v_val_1070_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v___x_1067_, 1);
return v_val_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1071_, lean_object* v_e_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Expr_fvarId_x21(v_e_1072_);
v___x_1074_ = l_Lean_LocalContext_get_x21(v_lctx_1071_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1075_, lean_object* v_e_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1075_, v_e_1076_);
lean_dec_ref(v_e_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1078_, lean_object* v_i_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_array_get_size(v_keys_1078_);
v___x_1082_ = lean_nat_dec_lt(v_i_1079_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v_i_1079_);
return v___x_1082_;
}
else
{
lean_object* v_k_x27_1083_; uint8_t v___x_1084_; 
v_k_x27_1083_ = lean_array_fget_borrowed(v_keys_1078_, v_i_1079_);
v___x_1084_ = l_Lean_instBEqFVarId_beq(v_k_1080_, v_k_x27_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_nat_add(v_i_1079_, v___x_1085_);
lean_dec(v_i_1079_);
v_i_1079_ = v___x_1086_;
goto _start;
}
else
{
lean_dec(v_i_1079_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1088_, lean_object* v_i_1089_, lean_object* v_k_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1088_, v_i_1089_, v_k_1090_);
lean_dec(v_k_1090_);
lean_dec_ref(v_keys_1088_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1093_, size_t v_x_1094_, lean_object* v_x_1095_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
lean_object* v_es_1096_; lean_object* v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v_j_1100_; lean_object* v___x_1101_; 
v_es_1096_ = lean_ctor_get(v_x_1093_, 0);
v___x_1097_ = lean_box(2);
v___x_1098_ = ((size_t)31ULL);
v___x_1099_ = lean_usize_land(v_x_1094_, v___x_1098_);
v_j_1100_ = lean_usize_to_nat(v___x_1099_);
v___x_1101_ = lean_array_get_borrowed(v___x_1097_, v_es_1096_, v_j_1100_);
lean_dec(v_j_1100_);
switch(lean_obj_tag(v___x_1101_))
{
case 0:
{
lean_object* v_key_1102_; uint8_t v___x_1103_; 
v_key_1102_ = lean_ctor_get(v___x_1101_, 0);
v___x_1103_ = l_Lean_instBEqFVarId_beq(v_x_1095_, v_key_1102_);
return v___x_1103_;
}
case 1:
{
lean_object* v_node_1104_; size_t v___x_1105_; size_t v___x_1106_; 
v_node_1104_ = lean_ctor_get(v___x_1101_, 0);
v___x_1105_ = ((size_t)5ULL);
v___x_1106_ = lean_usize_shift_right(v_x_1094_, v___x_1105_);
v_x_1093_ = v_node_1104_;
v_x_1094_ = v___x_1106_;
goto _start;
}
default: 
{
uint8_t v___x_1108_; 
v___x_1108_ = 0;
return v___x_1108_;
}
}
}
else
{
lean_object* v_ks_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_ks_1109_ = lean_ctor_get(v_x_1093_, 0);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1109_, v___x_1110_, v_x_1095_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
size_t v_x_119__boxed_1115_; uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_x_119__boxed_1115_ = lean_unbox_usize(v_x_1113_);
lean_dec(v_x_1113_);
v_res_1116_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1112_, v_x_119__boxed_1115_, v_x_1114_);
lean_dec(v_x_1114_);
lean_dec_ref(v_x_1112_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
uint64_t v___x_1120_; size_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_instHashableFVarId_hash(v_x_1119_);
v___x_1121_ = lean_uint64_to_usize(v___x_1120_);
v___x_1122_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1118_, v___x_1121_, v_x_1119_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1123_, v_x_1124_);
lean_dec(v_x_1124_);
lean_dec_ref(v_x_1123_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1127_, lean_object* v_fvarId_1128_){
_start:
{
lean_object* v_fvarIdToDecl_1129_; uint8_t v___x_1130_; 
v_fvarIdToDecl_1129_ = lean_ctor_get(v_lctx_1127_, 0);
v___x_1130_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1129_, v_fvarId_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1131_, lean_object* v_fvarId_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Lean_LocalContext_contains(v_lctx_1131_, v_fvarId_1132_);
lean_dec(v_fvarId_1132_);
lean_dec_ref(v_lctx_1131_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1139_, v_x_1140_, v_x_1141_);
lean_dec(v_x_1141_);
lean_dec_ref(v_x_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, size_t v_x_1146_, lean_object* v_x_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1145_, v_x_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
size_t v_x_182__boxed_1153_; uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_x_182__boxed_1153_ = lean_unbox_usize(v_x_1151_);
lean_dec(v_x_1151_);
v_res_1154_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1149_, v_x_1150_, v_x_182__boxed_1153_, v_x_1152_);
lean_dec(v_x_1152_);
lean_dec_ref(v_x_1150_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_heq_1159_, lean_object* v_i_1160_, lean_object* v_k_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1157_, v_i_1160_, v_k_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_heq_1166_, lean_object* v_i_1167_, lean_object* v_k_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1163_, v_keys_1164_, v_vals_1165_, v_heq_1166_, v_i_1167_, v_k_1168_);
lean_dec(v_k_1168_);
lean_dec_ref(v_vals_1165_);
lean_dec_ref(v_keys_1164_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1171_, lean_object* v_e_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = l_Lean_Expr_fvarId_x21(v_e_1172_);
v___x_1174_ = l_Lean_LocalContext_contains(v_lctx_1171_, v___x_1173_);
lean_dec(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1175_, lean_object* v_e_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Lean_LocalContext_containsFVar(v_lctx_1175_, v_e_1176_);
lean_dec_ref(v_e_1176_);
lean_dec_ref(v_lctx_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1179_, size_t v_i_1180_, size_t v_stop_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v___y_1184_; uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1180_, v_stop_1181_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_array_uget_borrowed(v_as_1179_, v_i_1180_);
if (lean_obj_tag(v___x_1189_) == 0)
{
v___y_1184_ = v_b_1182_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1190_; lean_object* v_fvarId_1191_; lean_object* v___x_1192_; 
v_val_1190_ = lean_ctor_get(v___x_1189_, 0);
v_fvarId_1191_ = lean_ctor_get(v_val_1190_, 1);
lean_inc(v_fvarId_1191_);
v___x_1192_ = lean_array_push(v_b_1182_, v_fvarId_1191_);
v___y_1184_ = v___x_1192_;
goto v___jp_1183_;
}
}
else
{
return v_b_1182_;
}
v___jp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1180_, v___x_1185_);
v_i_1180_ = v___x_1186_;
v_b_1182_ = v___y_1184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v_b_1196_){
_start:
{
size_t v_i_boxed_1197_; size_t v_stop_boxed_1198_; lean_object* v_res_1199_; 
v_i_boxed_1197_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1198_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1193_, v_i_boxed_1197_, v_stop_boxed_1198_, v_b_1196_);
lean_dec_ref(v_as_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
if (lean_obj_tag(v_x_1200_) == 0)
{
lean_object* v_cs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_cs_1202_ = lean_ctor_get(v_x_1200_, 0);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_cs_1202_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v_x_1201_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1204_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1202_, v___x_1206_, v___x_1207_, v_x_1201_);
return v___x_1208_;
}
}
else
{
lean_object* v_vs_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_vs_1209_ = lean_ctor_get(v_x_1200_, 0);
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_array_get_size(v_vs_1209_);
v___x_1212_ = lean_nat_dec_lt(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
return v_x_1201_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1211_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1209_, v___x_1213_, v___x_1214_, v_x_1201_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1216_, size_t v_i_1217_, size_t v_stop_1218_, lean_object* v_b_1219_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_eq(v_i_1217_, v_stop_1218_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; 
v___x_1221_ = lean_array_uget_borrowed(v_as_1216_, v_i_1217_);
v___x_1222_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1221_, v_b_1219_);
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1217_, v___x_1223_);
v_i_1217_ = v___x_1224_;
v_b_1219_ = v___x_1222_;
goto _start;
}
else
{
return v_b_1219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1226_, lean_object* v_i_1227_, lean_object* v_stop_1228_, lean_object* v_b_1229_){
_start:
{
size_t v_i_boxed_1230_; size_t v_stop_boxed_1231_; lean_object* v_res_1232_; 
v_i_boxed_1230_ = lean_unbox_usize(v_i_1227_);
lean_dec(v_i_1227_);
v_stop_boxed_1231_ = lean_unbox_usize(v_stop_1228_);
lean_dec(v_stop_1228_);
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1226_, v_i_boxed_1230_, v_stop_boxed_1231_, v_b_1229_);
lean_dec_ref(v_as_1226_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1233_, v_x_1234_);
lean_dec_ref(v_x_1233_);
return v_res_1235_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1237_, size_t v_x_1238_, size_t v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_cs_1241_; lean_object* v___x_1242_; size_t v___x_1243_; lean_object* v_j_1244_; lean_object* v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_cs_1241_ = lean_ctor_get(v_x_1237_, 0);
v___x_1242_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1243_ = lean_usize_shift_right(v_x_1238_, v_x_1239_);
v_j_1244_ = lean_usize_to_nat(v___x_1243_);
v___x_1245_ = lean_array_get_borrowed(v___x_1242_, v_cs_1241_, v_j_1244_);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_shift_left(v___x_1246_, v_x_1239_);
v___x_1248_ = lean_usize_sub(v___x_1247_, v___x_1246_);
v___x_1249_ = lean_usize_land(v_x_1238_, v___x_1248_);
v___x_1250_ = ((size_t)5ULL);
v___x_1251_ = lean_usize_sub(v_x_1239_, v___x_1250_);
v___x_1252_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1245_, v___x_1249_, v___x_1251_, v_x_1240_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_add(v_j_1244_, v___x_1253_);
lean_dec(v_j_1244_);
v___x_1255_ = lean_array_get_size(v_cs_1241_);
v___x_1256_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v___x_1254_);
return v___x_1252_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_usize_of_nat(v___x_1255_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1241_, v___x_1257_, v___x_1258_, v___x_1252_);
return v___x_1259_;
}
}
else
{
lean_object* v_vs_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_vs_1260_ = lean_ctor_get(v_x_1237_, 0);
v___x_1261_ = lean_usize_to_nat(v_x_1238_);
v___x_1262_ = lean_array_get_size(v_vs_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec(v___x_1261_);
return v_x_1240_;
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_usize_of_nat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_usize_of_nat(v___x_1262_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1260_, v___x_1264_, v___x_1265_, v_x_1240_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
size_t v_x_1260__boxed_1271_; size_t v_x_1261__boxed_1272_; lean_object* v_res_1273_; 
v_x_1260__boxed_1271_ = lean_unbox_usize(v_x_1268_);
lean_dec(v_x_1268_);
v_x_1261__boxed_1272_ = lean_unbox_usize(v_x_1269_);
lean_dec(v_x_1269_);
v_res_1273_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1267_, v_x_1260__boxed_1271_, v_x_1261__boxed_1272_, v_x_1270_);
lean_dec_ref(v_x_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1274_, lean_object* v_init_1275_, lean_object* v_start_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_nat_dec_eq(v_start_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v_root_1279_; lean_object* v_tail_1280_; size_t v_shift_1281_; lean_object* v_tailOff_1282_; uint8_t v___x_1283_; 
v_root_1279_ = lean_ctor_get(v_t_1274_, 0);
v_tail_1280_ = lean_ctor_get(v_t_1274_, 1);
v_shift_1281_ = lean_ctor_get_usize(v_t_1274_, 4);
v_tailOff_1282_ = lean_ctor_get(v_t_1274_, 3);
v___x_1283_ = lean_nat_dec_le(v_tailOff_1282_, v_start_1276_);
if (v___x_1283_ == 0)
{
size_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1284_ = lean_usize_of_nat(v_start_1276_);
v___x_1285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1279_, v___x_1284_, v_shift_1281_, v_init_1275_);
v___x_1286_ = lean_array_get_size(v_tail_1280_);
v___x_1287_ = lean_nat_dec_lt(v___x_1277_, v___x_1286_);
if (v___x_1287_ == 0)
{
return v___x_1285_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1286_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1288_, v___x_1289_, v___x_1285_);
return v___x_1290_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = lean_nat_sub(v_start_1276_, v_tailOff_1282_);
v___x_1292_ = lean_array_get_size(v_tail_1280_);
v___x_1293_ = lean_nat_dec_lt(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec(v___x_1291_);
return v_init_1275_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_usize_of_nat(v___x_1291_);
lean_dec(v___x_1291_);
v___x_1295_ = lean_usize_of_nat(v___x_1292_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1280_, v___x_1294_, v___x_1295_, v_init_1275_);
return v___x_1296_;
}
}
}
else
{
lean_object* v_root_1297_; lean_object* v_tail_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_root_1297_ = lean_ctor_get(v_t_1274_, 0);
v_tail_1298_ = lean_ctor_get(v_t_1274_, 1);
v___x_1299_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1297_, v_init_1275_);
v___x_1300_ = lean_array_get_size(v_tail_1298_);
v___x_1301_ = lean_nat_dec_lt(v___x_1277_, v___x_1300_);
if (v___x_1301_ == 0)
{
return v___x_1299_;
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = lean_usize_of_nat(v___x_1300_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1298_, v___x_1302_, v___x_1303_, v___x_1299_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1305_, lean_object* v_init_1306_, lean_object* v_start_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1305_, v_init_1306_, v_start_1307_);
lean_dec(v_start_1307_);
lean_dec_ref(v_t_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1311_){
_start:
{
lean_object* v_decls_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_decls_1312_ = lean_ctor_get(v_lctx_1311_, 1);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1315_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1312_, v___x_1314_, v___x_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_LocalContext_getFVarIds(v_lctx_1316_);
lean_dec_ref(v_lctx_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1318_, size_t v_i_1319_, lean_object* v_bs_1320_){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_usize_dec_lt(v_i_1319_, v_sz_1318_);
if (v___x_1321_ == 0)
{
return v_bs_1320_;
}
else
{
lean_object* v_v_1322_; lean_object* v___x_1323_; lean_object* v_bs_x27_1324_; lean_object* v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v_v_1322_ = lean_array_uget(v_bs_1320_, v_i_1319_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v_bs_x27_1324_ = lean_array_uset(v_bs_1320_, v_i_1319_, v___x_1323_);
v___x_1325_ = l_Lean_mkFVar(v_v_1322_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1319_, v___x_1326_);
v___x_1328_ = lean_array_uset(v_bs_x27_1324_, v_i_1319_, v___x_1325_);
v_i_1319_ = v___x_1327_;
v_bs_1320_ = v___x_1328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1330_, lean_object* v_i_1331_, lean_object* v_bs_1332_){
_start:
{
size_t v_sz_boxed_1333_; size_t v_i_boxed_1334_; lean_object* v_res_1335_; 
v_sz_boxed_1333_ = lean_unbox_usize(v_sz_1330_);
lean_dec(v_sz_1330_);
v_i_boxed_1334_ = lean_unbox_usize(v_i_1331_);
lean_dec(v_i_1331_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1333_, v_i_boxed_1334_, v_bs_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1336_){
_start:
{
lean_object* v___x_1337_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = l_Lean_LocalContext_getFVarIds(v_lctx_1336_);
v_sz_1338_ = lean_array_size(v___x_1337_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1338_, v___x_1339_, v___x_1337_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_LocalContext_getFVars(v_lctx_1341_);
lean_dec_ref(v_lctx_1341_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1343_){
_start:
{
lean_object* v_size_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_size_1344_ = lean_ctor_get(v_a_1343_, 2);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_nat_dec_eq(v_size_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_sub(v_size_1344_, v___x_1348_);
v___x_1350_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1347_, v_a_1343_, v___x_1349_);
lean_dec(v___x_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_PersistentArray_pop___redArg(v_a_1343_);
v_a_1343_ = v___x_1351_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1350_, 1);
return v_a_1343_;
}
}
else
{
return v_a_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1353_, lean_object* v_t_1354_){
_start:
{
if (lean_obj_tag(v_t_1354_) == 0)
{
lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_l_1357_; lean_object* v_r_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_2012_; 
v_k_1355_ = lean_ctor_get(v_t_1354_, 1);
v_v_1356_ = lean_ctor_get(v_t_1354_, 2);
v_l_1357_ = lean_ctor_get(v_t_1354_, 3);
v_r_1358_ = lean_ctor_get(v_t_1354_, 4);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_t_1354_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v_t_1354_, 0);
lean_dec(v_unused_2013_);
v___x_1360_ = v_t_1354_;
v_isShared_1361_ = v_isSharedCheck_2012_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_r_1358_);
lean_inc(v_l_1357_);
lean_inc(v_v_1356_);
lean_inc(v_k_1355_);
lean_dec(v_t_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_2012_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v___x_1362_; 
v___x_1362_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1353_, v_k_1355_);
switch(v___x_1362_)
{
case 0:
{
lean_object* v_impl_1363_; lean_object* v___x_1364_; 
v_impl_1363_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1353_, v_l_1357_);
v___x_1364_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1363_) == 0)
{
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_size_1365_; lean_object* v_size_1366_; lean_object* v_k_1367_; lean_object* v_v_1368_; lean_object* v_l_1369_; lean_object* v_r_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_size_1365_ = lean_ctor_get(v_impl_1363_, 0);
v_size_1366_ = lean_ctor_get(v_r_1358_, 0);
v_k_1367_ = lean_ctor_get(v_r_1358_, 1);
v_v_1368_ = lean_ctor_get(v_r_1358_, 2);
v_l_1369_ = lean_ctor_get(v_r_1358_, 3);
lean_inc(v_l_1369_);
v_r_1370_ = lean_ctor_get(v_r_1358_, 4);
v___x_1371_ = lean_unsigned_to_nat(3u);
v___x_1372_ = lean_nat_mul(v___x_1371_, v_size_1365_);
v___x_1373_ = lean_nat_dec_lt(v___x_1372_, v_size_1366_);
lean_dec(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_l_1369_);
v___x_1374_ = lean_nat_add(v___x_1364_, v_size_1365_);
v___x_1375_ = lean_nat_add(v___x_1374_, v_size_1366_);
lean_dec(v___x_1374_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 3, v_impl_1363_);
lean_ctor_set(v___x_1360_, 0, v___x_1375_);
v___x_1377_ = v___x_1360_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_impl_1363_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_r_1358_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1442_; 
lean_inc(v_r_1370_);
lean_inc(v_v_1368_);
lean_inc(v_k_1367_);
lean_inc(v_size_1366_);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1443_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_r_1358_, 2);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_r_1358_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1447_);
v___x_1380_ = v_r_1358_;
v_isShared_1381_ = v_isSharedCheck_1442_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_r_1358_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1442_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_size_1382_; lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v_l_1385_; lean_object* v_r_1386_; lean_object* v_size_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_size_1382_ = lean_ctor_get(v_l_1369_, 0);
v_k_1383_ = lean_ctor_get(v_l_1369_, 1);
v_v_1384_ = lean_ctor_get(v_l_1369_, 2);
v_l_1385_ = lean_ctor_get(v_l_1369_, 3);
v_r_1386_ = lean_ctor_get(v_l_1369_, 4);
v_size_1387_ = lean_ctor_get(v_r_1370_, 0);
v___x_1388_ = lean_unsigned_to_nat(2u);
v___x_1389_ = lean_nat_mul(v___x_1388_, v_size_1387_);
v___x_1390_ = lean_nat_dec_lt(v_size_1382_, v___x_1389_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1418_; 
lean_inc(v_r_1386_);
lean_inc(v_l_1385_);
lean_inc(v_v_1384_);
lean_inc(v_k_1383_);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_l_1369_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; lean_object* v_unused_1420_; lean_object* v_unused_1421_; lean_object* v_unused_1422_; lean_object* v_unused_1423_; 
v_unused_1419_ = lean_ctor_get(v_l_1369_, 4);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_l_1369_, 3);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_l_1369_, 2);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_l_1369_, 1);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_l_1369_, 0);
lean_dec(v_unused_1423_);
v___x_1392_ = v_l_1369_;
v_isShared_1393_ = v_isSharedCheck_1418_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_l_1369_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1418_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1408_; 
v___x_1394_ = lean_nat_add(v___x_1364_, v_size_1365_);
v___x_1395_ = lean_nat_add(v___x_1394_, v_size_1366_);
lean_dec(v_size_1366_);
if (lean_obj_tag(v_l_1385_) == 0)
{
lean_object* v_size_1416_; 
v_size_1416_ = lean_ctor_get(v_l_1385_, 0);
lean_inc(v_size_1416_);
v___y_1408_ = v_size_1416_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___y_1408_ = v___x_1417_;
goto v___jp_1407_;
}
v___jp_1396_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = lean_nat_add(v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec(v___y_1398_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_r_1370_);
lean_ctor_set(v___x_1392_, 3, v_r_1386_);
lean_ctor_set(v___x_1392_, 2, v_v_1368_);
lean_ctor_set(v___x_1392_, 1, v_k_1367_);
lean_ctor_set(v___x_1392_, 0, v___x_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_r_1386_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_r_1370_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v___x_1402_);
lean_ctor_set(v___x_1380_, 3, v___y_1397_);
lean_ctor_set(v___x_1380_, 2, v_v_1384_);
lean_ctor_set(v___x_1380_, 1, v_k_1383_);
lean_ctor_set(v___x_1380_, 0, v___x_1395_);
v___x_1404_ = v___x_1380_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v___y_1397_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_nat_add(v___x_1394_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec(v___x_1394_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_l_1385_);
lean_ctor_set(v___x_1360_, 3, v_impl_1363_);
lean_ctor_set(v___x_1360_, 0, v___x_1409_);
v___x_1411_ = v___x_1360_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_impl_1363_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_l_1385_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_nat_add(v___x_1364_, v_size_1387_);
if (lean_obj_tag(v_r_1386_) == 0)
{
lean_object* v_size_1413_; 
v_size_1413_ = lean_ctor_get(v_r_1386_, 0);
lean_inc(v_size_1413_);
v___y_1397_ = v___x_1411_;
v___y_1398_ = v___x_1412_;
v___y_1399_ = v_size_1413_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___y_1397_ = v___x_1411_;
v___y_1398_ = v___x_1412_;
v___y_1399_ = v___x_1414_;
goto v___jp_1396_;
}
}
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_del_object(v___x_1360_);
v___x_1424_ = lean_nat_add(v___x_1364_, v_size_1365_);
v___x_1425_ = lean_nat_add(v___x_1424_, v_size_1366_);
lean_dec(v_size_1366_);
v___x_1426_ = lean_nat_add(v___x_1424_, v_size_1382_);
lean_dec(v___x_1424_);
lean_inc_ref(v_impl_1363_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_l_1369_);
lean_ctor_set(v___x_1380_, 3, v_impl_1363_);
lean_ctor_set(v___x_1380_, 2, v_v_1356_);
lean_ctor_set(v___x_1380_, 1, v_k_1355_);
lean_ctor_set(v___x_1380_, 0, v___x_1426_);
v___x_1428_ = v___x_1380_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_impl_1363_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_l_1369_);
v___x_1428_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_isSharedCheck_1435_ = !lean_is_exclusive(v_impl_1363_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_impl_1363_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_impl_1363_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_impl_1363_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_impl_1363_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_impl_1363_, 0);
lean_dec(v_unused_1440_);
v___x_1430_ = v_impl_1363_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_impl_1363_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_r_1370_);
lean_ctor_set(v___x_1430_, 3, v___x_1428_);
lean_ctor_set(v___x_1430_, 2, v_v_1368_);
lean_ctor_set(v___x_1430_, 1, v_k_1367_);
lean_ctor_set(v___x_1430_, 0, v___x_1425_);
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_r_1370_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v_size_1448_ = lean_ctor_get(v_impl_1363_, 0);
v___x_1449_ = lean_nat_add(v___x_1364_, v_size_1448_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 3, v_impl_1363_);
lean_ctor_set(v___x_1360_, 0, v___x_1449_);
v___x_1451_ = v___x_1360_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_impl_1363_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_r_1358_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_l_1453_; 
v_l_1453_ = lean_ctor_get(v_r_1358_, 3);
lean_inc(v_l_1453_);
if (lean_obj_tag(v_l_1453_) == 0)
{
lean_object* v_r_1454_; 
v_r_1454_ = lean_ctor_get(v_r_1358_, 4);
lean_inc(v_r_1454_);
if (lean_obj_tag(v_r_1454_) == 0)
{
lean_object* v_size_1455_; lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1470_; 
v_size_1455_ = lean_ctor_get(v_r_1358_, 0);
v_k_1456_ = lean_ctor_get(v_r_1358_, 1);
v_v_1457_ = lean_ctor_get(v_r_1358_, 2);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1471_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1472_);
v___x_1459_ = v_r_1358_;
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
lean_inc(v_size_1455_);
lean_dec(v_r_1358_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_size_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v_size_1461_ = lean_ctor_get(v_l_1453_, 0);
v___x_1462_ = lean_nat_add(v___x_1364_, v_size_1455_);
lean_dec(v_size_1455_);
v___x_1463_ = lean_nat_add(v___x_1364_, v_size_1461_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_l_1453_);
lean_ctor_set(v___x_1459_, 3, v_impl_1363_);
lean_ctor_set(v___x_1459_, 2, v_v_1356_);
lean_ctor_set(v___x_1459_, 1, v_k_1355_);
lean_ctor_set(v___x_1459_, 0, v___x_1463_);
v___x_1465_ = v___x_1459_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_impl_1363_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_l_1453_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_r_1454_);
lean_ctor_set(v___x_1360_, 3, v___x_1465_);
lean_ctor_set(v___x_1360_, 2, v_v_1457_);
lean_ctor_set(v___x_1360_, 1, v_k_1456_);
lean_ctor_set(v___x_1360_, 0, v___x_1462_);
v___x_1467_ = v___x_1360_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_r_1454_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_k_1473_; lean_object* v_v_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1497_; 
v_k_1473_ = lean_ctor_get(v_r_1358_, 1);
v_v_1474_ = lean_ctor_get(v_r_1358_, 2);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; 
v_unused_1498_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1500_);
v___x_1476_ = v_r_1358_;
v_isShared_1477_ = v_isSharedCheck_1497_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_v_1474_);
lean_inc(v_k_1473_);
lean_dec(v_r_1358_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1497_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_k_1478_; lean_object* v_v_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1493_; 
v_k_1478_ = lean_ctor_get(v_l_1453_, 1);
v_v_1479_ = lean_ctor_get(v_l_1453_, 2);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_l_1453_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1494_ = lean_ctor_get(v_l_1453_, 4);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1453_, 3);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1453_, 0);
lean_dec(v_unused_1496_);
v___x_1481_ = v_l_1453_;
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_v_1479_);
lean_inc(v_k_1478_);
lean_dec(v_l_1453_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_unsigned_to_nat(3u);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1454_);
lean_ctor_set(v___x_1481_, 3, v_r_1454_);
lean_ctor_set(v___x_1481_, 2, v_v_1356_);
lean_ctor_set(v___x_1481_, 1, v_k_1355_);
lean_ctor_set(v___x_1481_, 0, v___x_1364_);
v___x_1485_ = v___x_1481_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_r_1454_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_r_1454_);
v___x_1485_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 3, v_r_1454_);
lean_ctor_set(v___x_1476_, 0, v___x_1364_);
v___x_1487_ = v___x_1476_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1473_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1474_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_r_1454_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1454_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v___x_1487_);
lean_ctor_set(v___x_1360_, 3, v___x_1485_);
lean_ctor_set(v___x_1360_, 2, v_v_1479_);
lean_ctor_set(v___x_1360_, 1, v_k_1478_);
lean_ctor_set(v___x_1360_, 0, v___x_1483_);
v___x_1489_ = v___x_1360_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1479_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1501_; 
v_r_1501_ = lean_ctor_get(v_r_1358_, 4);
lean_inc(v_r_1501_);
if (lean_obj_tag(v_r_1501_) == 0)
{
lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1514_; 
v_k_1502_ = lean_ctor_get(v_r_1358_, 1);
v_v_1503_ = lean_ctor_get(v_r_1358_, 2);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; 
v_unused_1515_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1517_);
v___x_1505_ = v_r_1358_;
v_isShared_1506_ = v_isSharedCheck_1514_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_v_1503_);
lean_inc(v_k_1502_);
lean_dec(v_r_1358_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1514_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_unsigned_to_nat(3u);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_l_1453_);
lean_ctor_set(v___x_1505_, 2, v_v_1356_);
lean_ctor_set(v___x_1505_, 1, v_k_1355_);
lean_ctor_set(v___x_1505_, 0, v___x_1364_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_l_1453_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_l_1453_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_r_1501_);
lean_ctor_set(v___x_1360_, 3, v___x_1509_);
lean_ctor_set(v___x_1360_, 2, v_v_1503_);
lean_ctor_set(v___x_1360_, 1, v_k_1502_);
lean_ctor_set(v___x_1360_, 0, v___x_1507_);
v___x_1511_ = v___x_1360_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_r_1501_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_size_1518_; lean_object* v_k_1519_; lean_object* v_v_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1531_; 
v_size_1518_ = lean_ctor_get(v_r_1358_, 0);
v_k_1519_ = lean_ctor_get(v_r_1358_, 1);
v_v_1520_ = lean_ctor_get(v_r_1358_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; 
v_unused_1532_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1533_);
v___x_1522_ = v_r_1358_;
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_v_1520_);
lean_inc(v_k_1519_);
lean_inc(v_size_1518_);
lean_dec(v_r_1358_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 3, v_r_1501_);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_size_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1520_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1501_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1501_);
v___x_1525_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_unsigned_to_nat(2u);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v___x_1525_);
lean_ctor_set(v___x_1360_, 3, v_r_1501_);
lean_ctor_set(v___x_1360_, 0, v___x_1526_);
v___x_1528_ = v___x_1360_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_r_1501_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1525_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
else
{
lean_object* v___x_1535_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 3, v_r_1358_);
lean_ctor_set(v___x_1360_, 0, v___x_1364_);
v___x_1535_ = v___x_1360_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_r_1358_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_r_1358_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1360_);
lean_dec(v_v_1356_);
lean_dec(v_k_1355_);
if (lean_obj_tag(v_l_1357_) == 0)
{
if (lean_obj_tag(v_r_1358_) == 0)
{
lean_object* v_size_1537_; lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_l_1540_; lean_object* v_r_1541_; lean_object* v_size_1542_; lean_object* v_k_1543_; lean_object* v_v_1544_; lean_object* v_l_1545_; lean_object* v_r_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_size_1537_ = lean_ctor_get(v_l_1357_, 0);
v_k_1538_ = lean_ctor_get(v_l_1357_, 1);
v_v_1539_ = lean_ctor_get(v_l_1357_, 2);
v_l_1540_ = lean_ctor_get(v_l_1357_, 3);
v_r_1541_ = lean_ctor_get(v_l_1357_, 4);
lean_inc(v_r_1541_);
v_size_1542_ = lean_ctor_get(v_r_1358_, 0);
v_k_1543_ = lean_ctor_get(v_r_1358_, 1);
v_v_1544_ = lean_ctor_get(v_r_1358_, 2);
v_l_1545_ = lean_ctor_get(v_r_1358_, 3);
lean_inc(v_l_1545_);
v_r_1546_ = lean_ctor_get(v_r_1358_, 4);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_dec_lt(v_size_1537_, v_size_1542_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1684_; 
lean_inc(v_l_1540_);
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1685_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1689_);
v___x_1550_ = v_l_1357_;
v_isShared_1551_ = v_isSharedCheck_1684_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_l_1357_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1684_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v_tree_1553_; 
v___x_1552_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1538_, v_v_1539_, v_l_1540_, v_r_1541_);
v_tree_1553_ = lean_ctor_get(v___x_1552_, 2);
if (lean_obj_tag(v_tree_1553_) == 0)
{
lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v_size_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
lean_inc_ref(v_tree_1553_);
v_k_1554_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_k_1554_);
v_v_1555_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_v_1555_);
lean_dec_ref(v___x_1552_);
v_size_1556_ = lean_ctor_get(v_tree_1553_, 0);
v___x_1557_ = lean_unsigned_to_nat(3u);
v___x_1558_ = lean_nat_mul(v___x_1557_, v_size_1556_);
v___x_1559_ = lean_nat_dec_lt(v___x_1558_, v_size_1542_);
lean_dec(v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec(v_l_1545_);
v___x_1560_ = lean_nat_add(v___x_1547_, v_size_1556_);
v___x_1561_ = lean_nat_add(v___x_1560_, v_size_1542_);
lean_dec(v___x_1560_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_r_1358_);
lean_ctor_set(v___x_1550_, 3, v_tree_1553_);
lean_ctor_set(v___x_1550_, 2, v_v_1555_);
lean_ctor_set(v___x_1550_, 1, v_k_1554_);
lean_ctor_set(v___x_1550_, 0, v___x_1561_);
v___x_1563_ = v___x_1550_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_tree_1553_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_r_1358_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
else
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1619_; 
lean_inc(v_r_1546_);
lean_inc(v_v_1544_);
lean_inc(v_k_1543_);
lean_inc(v_size_1542_);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; 
v_unused_1620_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_r_1358_, 2);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_r_1358_, 1);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1624_);
v___x_1566_ = v_r_1358_;
v_isShared_1567_ = v_isSharedCheck_1619_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_r_1358_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1619_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_size_1568_; lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_l_1571_; lean_object* v_r_1572_; lean_object* v_size_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_size_1568_ = lean_ctor_get(v_l_1545_, 0);
v_k_1569_ = lean_ctor_get(v_l_1545_, 1);
v_v_1570_ = lean_ctor_get(v_l_1545_, 2);
v_l_1571_ = lean_ctor_get(v_l_1545_, 3);
v_r_1572_ = lean_ctor_get(v_l_1545_, 4);
v_size_1573_ = lean_ctor_get(v_r_1546_, 0);
v___x_1574_ = lean_unsigned_to_nat(2u);
v___x_1575_ = lean_nat_mul(v___x_1574_, v_size_1573_);
v___x_1576_ = lean_nat_dec_lt(v_size_1568_, v___x_1575_);
lean_dec(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1604_; 
lean_inc(v_r_1572_);
lean_inc(v_l_1571_);
lean_inc(v_v_1570_);
lean_inc(v_k_1569_);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_l_1545_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1605_ = lean_ctor_get(v_l_1545_, 4);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1545_, 3);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1545_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_l_1545_, 1);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_l_1545_, 0);
lean_dec(v_unused_1609_);
v___x_1578_ = v_l_1545_;
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v_l_1545_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1594_; 
v___x_1580_ = lean_nat_add(v___x_1547_, v_size_1556_);
v___x_1581_ = lean_nat_add(v___x_1580_, v_size_1542_);
lean_dec(v_size_1542_);
if (lean_obj_tag(v_l_1571_) == 0)
{
lean_object* v_size_1602_; 
v_size_1602_ = lean_ctor_get(v_l_1571_, 0);
lean_inc(v_size_1602_);
v___y_1594_ = v_size_1602_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_unsigned_to_nat(0u);
v___y_1594_ = v___x_1603_;
goto v___jp_1593_;
}
v___jp_1582_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_nat_add(v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec(v___y_1584_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 4, v_r_1546_);
lean_ctor_set(v___x_1578_, 3, v_r_1572_);
lean_ctor_set(v___x_1578_, 2, v_v_1544_);
lean_ctor_set(v___x_1578_, 1, v_k_1543_);
lean_ctor_set(v___x_1578_, 0, v___x_1586_);
v___x_1588_ = v___x_1578_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_r_1572_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_r_1546_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v___x_1588_);
lean_ctor_set(v___x_1566_, 3, v___y_1583_);
lean_ctor_set(v___x_1566_, 2, v_v_1570_);
lean_ctor_set(v___x_1566_, 1, v_k_1569_);
lean_ctor_set(v___x_1566_, 0, v___x_1581_);
v___x_1590_ = v___x_1566_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1569_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1570_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v___y_1583_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_nat_add(v___x_1580_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec(v___x_1580_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_l_1571_);
lean_ctor_set(v___x_1550_, 3, v_tree_1553_);
lean_ctor_set(v___x_1550_, 2, v_v_1555_);
lean_ctor_set(v___x_1550_, 1, v_k_1554_);
lean_ctor_set(v___x_1550_, 0, v___x_1595_);
v___x_1597_ = v___x_1550_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_tree_1553_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1571_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_nat_add(v___x_1547_, v_size_1573_);
if (lean_obj_tag(v_r_1572_) == 0)
{
lean_object* v_size_1599_; 
v_size_1599_ = lean_ctor_get(v_r_1572_, 0);
lean_inc(v_size_1599_);
v___y_1583_ = v___x_1597_;
v___y_1584_ = v___x_1598_;
v___y_1585_ = v_size_1599_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
v___y_1583_ = v___x_1597_;
v___y_1584_ = v___x_1598_;
v___y_1585_ = v___x_1600_;
goto v___jp_1582_;
}
}
}
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1610_ = lean_nat_add(v___x_1547_, v_size_1556_);
v___x_1611_ = lean_nat_add(v___x_1610_, v_size_1542_);
lean_dec(v_size_1542_);
v___x_1612_ = lean_nat_add(v___x_1610_, v_size_1568_);
lean_dec(v___x_1610_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_l_1545_);
lean_ctor_set(v___x_1566_, 3, v_tree_1553_);
lean_ctor_set(v___x_1566_, 2, v_v_1555_);
lean_ctor_set(v___x_1566_, 1, v_k_1554_);
lean_ctor_set(v___x_1566_, 0, v___x_1612_);
v___x_1614_ = v___x_1566_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_tree_1553_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_l_1545_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_r_1546_);
lean_ctor_set(v___x_1550_, 3, v___x_1614_);
lean_ctor_set(v___x_1550_, 2, v_v_1544_);
lean_ctor_set(v___x_1550_, 1, v_k_1543_);
lean_ctor_set(v___x_1550_, 0, v___x_1611_);
v___x_1616_ = v___x_1550_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_r_1546_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
}
else
{
lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1678_; 
lean_inc(v_r_1546_);
lean_inc(v_v_1544_);
lean_inc(v_k_1543_);
lean_inc(v_size_1542_);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1679_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_r_1358_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_r_1358_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1683_);
v___x_1626_ = v_r_1358_;
v_isShared_1627_ = v_isSharedCheck_1678_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v_r_1358_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1678_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
if (lean_obj_tag(v_l_1545_) == 0)
{
if (lean_obj_tag(v_r_1546_) == 0)
{
lean_object* v_k_1628_; lean_object* v_v_1629_; lean_object* v_size_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_inc(v_tree_1553_);
v_k_1628_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_k_1628_);
v_v_1629_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_v_1629_);
lean_dec_ref(v___x_1552_);
v_size_1630_ = lean_ctor_get(v_l_1545_, 0);
v___x_1631_ = lean_nat_add(v___x_1547_, v_size_1542_);
lean_dec(v_size_1542_);
v___x_1632_ = lean_nat_add(v___x_1547_, v_size_1630_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 4, v_l_1545_);
lean_ctor_set(v___x_1626_, 3, v_tree_1553_);
lean_ctor_set(v___x_1626_, 2, v_v_1629_);
lean_ctor_set(v___x_1626_, 1, v_k_1628_);
lean_ctor_set(v___x_1626_, 0, v___x_1632_);
v___x_1634_ = v___x_1626_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_tree_1553_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_l_1545_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_r_1546_);
lean_ctor_set(v___x_1550_, 3, v___x_1634_);
lean_ctor_set(v___x_1550_, 2, v_v_1544_);
lean_ctor_set(v___x_1550_, 1, v_k_1543_);
lean_ctor_set(v___x_1550_, 0, v___x_1631_);
v___x_1636_ = v___x_1550_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_r_1546_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_k_1639_; lean_object* v_v_1640_; lean_object* v_k_1641_; lean_object* v_v_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_size_1542_);
v_k_1639_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_k_1639_);
v_v_1640_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_v_1640_);
lean_dec_ref(v___x_1552_);
v_k_1641_ = lean_ctor_get(v_l_1545_, 1);
v_v_1642_ = lean_ctor_get(v_l_1545_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_l_1545_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; lean_object* v_unused_1659_; 
v_unused_1657_ = lean_ctor_get(v_l_1545_, 4);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_l_1545_, 3);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_l_1545_, 0);
lean_dec(v_unused_1659_);
v___x_1644_ = v_l_1545_;
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_v_1642_);
lean_inc(v_k_1641_);
lean_dec(v_l_1545_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(3u);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v_r_1546_);
lean_ctor_set(v___x_1644_, 3, v_r_1546_);
lean_ctor_set(v___x_1644_, 2, v_v_1640_);
lean_ctor_set(v___x_1644_, 1, v_k_1639_);
lean_ctor_set(v___x_1644_, 0, v___x_1547_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1639_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1640_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_r_1546_);
v___x_1648_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 3, v_r_1546_);
lean_ctor_set(v___x_1626_, 0, v___x_1547_);
v___x_1650_ = v___x_1626_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_r_1546_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___x_1650_);
lean_ctor_set(v___x_1550_, 3, v___x_1648_);
lean_ctor_set(v___x_1550_, 2, v_v_1642_);
lean_ctor_set(v___x_1550_, 1, v_k_1641_);
lean_ctor_set(v___x_1550_, 0, v___x_1646_);
v___x_1652_ = v___x_1550_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1641_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1642_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1546_) == 0)
{
lean_object* v_k_1660_; lean_object* v_v_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_dec(v_size_1542_);
v_k_1660_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_k_1660_);
v_v_1661_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_v_1661_);
lean_dec_ref(v___x_1552_);
v___x_1662_ = lean_unsigned_to_nat(3u);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 4, v_l_1545_);
lean_ctor_set(v___x_1626_, 2, v_v_1661_);
lean_ctor_set(v___x_1626_, 1, v_k_1660_);
lean_ctor_set(v___x_1626_, 0, v___x_1547_);
v___x_1664_ = v___x_1626_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_l_1545_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_r_1546_);
lean_ctor_set(v___x_1550_, 3, v___x_1664_);
lean_ctor_set(v___x_1550_, 2, v_v_1544_);
lean_ctor_set(v___x_1550_, 1, v_k_1543_);
lean_ctor_set(v___x_1550_, 0, v___x_1662_);
v___x_1666_ = v___x_1550_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_r_1546_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_k_1669_; lean_object* v_v_1670_; lean_object* v___x_1672_; 
v_k_1669_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_k_1669_);
v_v_1670_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_v_1670_);
lean_dec_ref(v___x_1552_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 3, v_r_1546_);
v___x_1672_ = v___x_1626_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_size_1542_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_r_1546_);
v___x_1672_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_unsigned_to_nat(2u);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___x_1672_);
lean_ctor_set(v___x_1550_, 3, v_r_1546_);
lean_ctor_set(v___x_1550_, 2, v_v_1670_);
lean_ctor_set(v___x_1550_, 1, v_k_1669_);
lean_ctor_set(v___x_1550_, 0, v___x_1673_);
v___x_1675_ = v___x_1550_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v___x_1672_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1842_; 
lean_inc(v_r_1546_);
lean_inc(v_v_1544_);
lean_inc(v_k_1543_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_r_1358_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; 
v_unused_1843_ = lean_ctor_get(v_r_1358_, 4);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_r_1358_, 3);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_r_1358_, 2);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_r_1358_, 1);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v_r_1358_, 0);
lean_dec(v_unused_1847_);
v___x_1691_ = v_r_1358_;
v_isShared_1692_ = v_isSharedCheck_1842_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v_r_1358_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1842_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v_tree_1694_; 
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1543_, v_v_1544_, v_l_1545_, v_r_1546_);
v_tree_1694_ = lean_ctor_get(v___x_1693_, 2);
lean_inc(v_tree_1694_);
if (lean_obj_tag(v_tree_1694_) == 0)
{
lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v_size_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_k_1695_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_k_1695_);
v_v_1696_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_v_1696_);
lean_dec_ref(v___x_1693_);
v_size_1697_ = lean_ctor_get(v_tree_1694_, 0);
v___x_1698_ = lean_unsigned_to_nat(3u);
v___x_1699_ = lean_nat_mul(v___x_1698_, v_size_1697_);
v___x_1700_ = lean_nat_dec_lt(v___x_1699_, v_size_1537_);
lean_dec(v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_dec(v_r_1541_);
v___x_1701_ = lean_nat_add(v___x_1547_, v_size_1537_);
v___x_1702_ = lean_nat_add(v___x_1701_, v_size_1697_);
lean_dec(v___x_1701_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_tree_1694_);
lean_ctor_set(v___x_1691_, 3, v_l_1357_);
lean_ctor_set(v___x_1691_, 2, v_v_1696_);
lean_ctor_set(v___x_1691_, 1, v_k_1695_);
lean_ctor_set(v___x_1691_, 0, v___x_1702_);
v___x_1704_ = v___x_1691_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v_tree_1694_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1771_; 
lean_inc(v_l_1540_);
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
lean_inc(v_size_1537_);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1772_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1776_);
v___x_1707_ = v_l_1357_;
v_isShared_1708_ = v_isSharedCheck_1771_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_l_1357_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1771_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_size_1709_; lean_object* v_size_1710_; lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v_l_1713_; lean_object* v_r_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_size_1709_ = lean_ctor_get(v_l_1540_, 0);
v_size_1710_ = lean_ctor_get(v_r_1541_, 0);
v_k_1711_ = lean_ctor_get(v_r_1541_, 1);
v_v_1712_ = lean_ctor_get(v_r_1541_, 2);
v_l_1713_ = lean_ctor_get(v_r_1541_, 3);
v_r_1714_ = lean_ctor_get(v_r_1541_, 4);
v___x_1715_ = lean_unsigned_to_nat(2u);
v___x_1716_ = lean_nat_mul(v___x_1715_, v_size_1709_);
v___x_1717_ = lean_nat_dec_lt(v_size_1710_, v___x_1716_);
lean_dec(v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1755_; 
lean_inc(v_r_1714_);
lean_inc(v_l_1713_);
lean_inc(v_v_1712_);
lean_inc(v_k_1711_);
lean_del_object(v___x_1707_);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_r_1541_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1756_ = lean_ctor_get(v_r_1541_, 4);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_r_1541_, 3);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_r_1541_, 2);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_r_1541_, 1);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_r_1541_, 0);
lean_dec(v_unused_1760_);
v___x_1719_ = v_r_1541_;
v_isShared_1720_ = v_isSharedCheck_1755_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_r_1541_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1755_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___x_1743_; lean_object* v___y_1745_; 
v___x_1721_ = lean_nat_add(v___x_1547_, v_size_1537_);
lean_dec(v_size_1537_);
v___x_1722_ = lean_nat_add(v___x_1721_, v_size_1697_);
lean_dec(v___x_1721_);
v___x_1743_ = lean_nat_add(v___x_1547_, v_size_1709_);
if (lean_obj_tag(v_l_1713_) == 0)
{
lean_object* v_size_1753_; 
v_size_1753_ = lean_ctor_get(v_l_1713_, 0);
lean_inc(v_size_1753_);
v___y_1745_ = v_size_1753_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___y_1745_ = v___x_1754_;
goto v___jp_1744_;
}
v___jp_1723_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = lean_nat_add(v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec(v___y_1725_);
lean_inc_ref(v_tree_1694_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v_tree_1694_);
lean_ctor_set(v___x_1719_, 3, v_r_1714_);
lean_ctor_set(v___x_1719_, 2, v_v_1696_);
lean_ctor_set(v___x_1719_, 1, v_k_1695_);
lean_ctor_set(v___x_1719_, 0, v___x_1727_);
v___x_1729_ = v___x_1719_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_r_1714_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_tree_1694_);
v___x_1729_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_isSharedCheck_1736_ = !lean_is_exclusive(v_tree_1694_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; lean_object* v_unused_1739_; lean_object* v_unused_1740_; lean_object* v_unused_1741_; 
v_unused_1737_ = lean_ctor_get(v_tree_1694_, 4);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_tree_1694_, 3);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v_tree_1694_, 2);
lean_dec(v_unused_1739_);
v_unused_1740_ = lean_ctor_get(v_tree_1694_, 1);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v_tree_1694_, 0);
lean_dec(v_unused_1741_);
v___x_1731_ = v_tree_1694_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v_tree_1694_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 4, v___x_1729_);
lean_ctor_set(v___x_1731_, 3, v___y_1724_);
lean_ctor_set(v___x_1731_, 2, v_v_1712_);
lean_ctor_set(v___x_1731_, 1, v_k_1711_);
lean_ctor_set(v___x_1731_, 0, v___x_1722_);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v___y_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v___x_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
v___jp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_nat_add(v___x_1743_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec(v___x_1743_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_l_1713_);
lean_ctor_set(v___x_1691_, 3, v_l_1540_);
lean_ctor_set(v___x_1691_, 2, v_v_1539_);
lean_ctor_set(v___x_1691_, 1, v_k_1538_);
lean_ctor_set(v___x_1691_, 0, v___x_1746_);
v___x_1748_ = v___x_1691_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_l_1713_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_nat_add(v___x_1547_, v_size_1697_);
if (lean_obj_tag(v_r_1714_) == 0)
{
lean_object* v_size_1750_; 
v_size_1750_ = lean_ctor_get(v_r_1714_, 0);
lean_inc(v_size_1750_);
v___y_1724_ = v___x_1748_;
v___y_1725_ = v___x_1749_;
v___y_1726_ = v_size_1750_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___y_1724_ = v___x_1748_;
v___y_1725_ = v___x_1749_;
v___y_1726_ = v___x_1751_;
goto v___jp_1723_;
}
}
}
}
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1761_ = lean_nat_add(v___x_1547_, v_size_1537_);
lean_dec(v_size_1537_);
v___x_1762_ = lean_nat_add(v___x_1761_, v_size_1697_);
lean_dec(v___x_1761_);
v___x_1763_ = lean_nat_add(v___x_1547_, v_size_1697_);
v___x_1764_ = lean_nat_add(v___x_1763_, v_size_1710_);
lean_dec(v___x_1763_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_tree_1694_);
lean_ctor_set(v___x_1691_, 3, v_r_1541_);
lean_ctor_set(v___x_1691_, 2, v_v_1696_);
lean_ctor_set(v___x_1691_, 1, v_k_1695_);
lean_ctor_set(v___x_1691_, 0, v___x_1764_);
v___x_1766_ = v___x_1691_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_tree_1694_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v___x_1766_);
lean_ctor_set(v___x_1707_, 0, v___x_1762_);
v___x_1768_ = v___x_1707_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1540_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1800_; 
lean_inc_ref(v_l_1540_);
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
lean_inc(v_size_1537_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; 
v_unused_1801_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1805_);
v___x_1778_ = v_l_1357_;
v_isShared_1779_ = v_isSharedCheck_1800_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v_l_1357_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1800_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
if (lean_obj_tag(v_r_1541_) == 0)
{
lean_object* v_k_1780_; lean_object* v_v_1781_; lean_object* v_size_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v_k_1780_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_k_1780_);
v_v_1781_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_v_1781_);
lean_dec_ref(v___x_1693_);
v_size_1782_ = lean_ctor_get(v_r_1541_, 0);
v___x_1783_ = lean_nat_add(v___x_1547_, v_size_1537_);
lean_dec(v_size_1537_);
v___x_1784_ = lean_nat_add(v___x_1547_, v_size_1782_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_tree_1694_);
lean_ctor_set(v___x_1691_, 3, v_r_1541_);
lean_ctor_set(v___x_1691_, 2, v_v_1781_);
lean_ctor_set(v___x_1691_, 1, v_k_1780_);
lean_ctor_set(v___x_1691_, 0, v___x_1784_);
v___x_1786_ = v___x_1691_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_k_1780_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_v_1781_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_tree_1694_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 4, v___x_1786_);
lean_ctor_set(v___x_1778_, 0, v___x_1783_);
v___x_1788_ = v___x_1778_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_k_1791_; lean_object* v_v_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec(v_size_1537_);
v_k_1791_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_k_1791_);
v_v_1792_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_v_1792_);
lean_dec_ref(v___x_1693_);
v___x_1793_ = lean_unsigned_to_nat(3u);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_r_1541_);
lean_ctor_set(v___x_1691_, 3, v_r_1541_);
lean_ctor_set(v___x_1691_, 2, v_v_1792_);
lean_ctor_set(v___x_1691_, 1, v_k_1791_);
lean_ctor_set(v___x_1691_, 0, v___x_1547_);
v___x_1795_ = v___x_1691_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_r_1541_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 4, v___x_1795_);
lean_ctor_set(v___x_1778_, 0, v___x_1793_);
v___x_1797_ = v___x_1778_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1541_) == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1830_; 
lean_inc(v_l_1540_);
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; lean_object* v_unused_1835_; 
v_unused_1831_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1835_);
v___x_1807_ = v_l_1357_;
v_isShared_1808_ = v_isSharedCheck_1830_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v_l_1357_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1830_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_k_1809_; lean_object* v_v_1810_; lean_object* v_k_1811_; lean_object* v_v_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1826_; 
v_k_1809_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_k_1809_);
v_v_1810_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_v_1810_);
lean_dec_ref(v___x_1693_);
v_k_1811_ = lean_ctor_get(v_r_1541_, 1);
v_v_1812_ = lean_ctor_get(v_r_1541_, 2);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_r_1541_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1827_ = lean_ctor_get(v_r_1541_, 4);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_r_1541_, 3);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_r_1541_, 0);
lean_dec(v_unused_1829_);
v___x_1814_ = v_r_1541_;
v_isShared_1815_ = v_isSharedCheck_1826_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_v_1812_);
lean_inc(v_k_1811_);
lean_dec(v_r_1541_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1826_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(3u);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 4, v_l_1540_);
lean_ctor_set(v___x_1814_, 3, v_l_1540_);
lean_ctor_set(v___x_1814_, 2, v_v_1539_);
lean_ctor_set(v___x_1814_, 1, v_k_1538_);
lean_ctor_set(v___x_1814_, 0, v___x_1547_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v_l_1540_);
v___x_1818_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_l_1540_);
lean_ctor_set(v___x_1691_, 3, v_l_1540_);
lean_ctor_set(v___x_1691_, 2, v_v_1810_);
lean_ctor_set(v___x_1691_, 1, v_k_1809_);
lean_ctor_set(v___x_1691_, 0, v___x_1547_);
v___x_1820_ = v___x_1691_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_k_1809_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_v_1810_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_l_1540_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_l_1540_);
v___x_1820_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 4, v___x_1820_);
lean_ctor_set(v___x_1807_, 3, v___x_1818_);
lean_ctor_set(v___x_1807_, 2, v_v_1812_);
lean_ctor_set(v___x_1807_, 1, v_k_1811_);
lean_ctor_set(v___x_1807_, 0, v___x_1816_);
v___x_1822_ = v___x_1807_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
else
{
lean_object* v_k_1836_; lean_object* v_v_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_k_1836_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_k_1836_);
v_v_1837_ = lean_ctor_get(v___x_1693_, 1);
lean_inc(v_v_1837_);
lean_dec_ref(v___x_1693_);
v___x_1838_ = lean_unsigned_to_nat(2u);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_r_1541_);
lean_ctor_set(v___x_1691_, 3, v_l_1357_);
lean_ctor_set(v___x_1691_, 2, v_v_1837_);
lean_ctor_set(v___x_1691_, 1, v_k_1836_);
lean_ctor_set(v___x_1691_, 0, v___x_1838_);
v___x_1840_ = v___x_1691_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_k_1836_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_v_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_r_1541_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
}
else
{
return v_l_1357_;
}
}
else
{
return v_r_1358_;
}
}
default: 
{
lean_object* v_impl_1848_; lean_object* v___x_1849_; 
v_impl_1848_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1353_, v_r_1358_);
v___x_1849_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1848_) == 0)
{
if (lean_obj_tag(v_l_1357_) == 0)
{
lean_object* v_size_1850_; lean_object* v_size_1851_; lean_object* v_k_1852_; lean_object* v_v_1853_; lean_object* v_l_1854_; lean_object* v_r_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_size_1850_ = lean_ctor_get(v_impl_1848_, 0);
v_size_1851_ = lean_ctor_get(v_l_1357_, 0);
v_k_1852_ = lean_ctor_get(v_l_1357_, 1);
v_v_1853_ = lean_ctor_get(v_l_1357_, 2);
v_l_1854_ = lean_ctor_get(v_l_1357_, 3);
v_r_1855_ = lean_ctor_get(v_l_1357_, 4);
lean_inc(v_r_1855_);
v___x_1856_ = lean_unsigned_to_nat(3u);
v___x_1857_ = lean_nat_mul(v___x_1856_, v_size_1850_);
v___x_1858_ = lean_nat_dec_lt(v___x_1857_, v_size_1851_);
lean_dec(v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec(v_r_1855_);
v___x_1859_ = lean_nat_add(v___x_1849_, v_size_1851_);
v___x_1860_ = lean_nat_add(v___x_1859_, v_size_1850_);
lean_dec(v___x_1859_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_impl_1848_);
lean_ctor_set(v___x_1360_, 0, v___x_1860_);
v___x_1862_ = v___x_1360_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_impl_1848_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1929_; 
lean_inc(v_l_1854_);
lean_inc(v_v_1853_);
lean_inc(v_k_1852_);
lean_inc(v_size_1851_);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; lean_object* v_unused_1931_; lean_object* v_unused_1932_; lean_object* v_unused_1933_; lean_object* v_unused_1934_; 
v_unused_1930_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1934_);
v___x_1865_ = v_l_1357_;
v_isShared_1866_ = v_isSharedCheck_1929_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_l_1357_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1929_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_size_1867_; lean_object* v_size_1868_; lean_object* v_k_1869_; lean_object* v_v_1870_; lean_object* v_l_1871_; lean_object* v_r_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_size_1867_ = lean_ctor_get(v_l_1854_, 0);
v_size_1868_ = lean_ctor_get(v_r_1855_, 0);
v_k_1869_ = lean_ctor_get(v_r_1855_, 1);
v_v_1870_ = lean_ctor_get(v_r_1855_, 2);
v_l_1871_ = lean_ctor_get(v_r_1855_, 3);
v_r_1872_ = lean_ctor_get(v_r_1855_, 4);
v___x_1873_ = lean_unsigned_to_nat(2u);
v___x_1874_ = lean_nat_mul(v___x_1873_, v_size_1867_);
v___x_1875_ = lean_nat_dec_lt(v_size_1868_, v___x_1874_);
lean_dec(v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1904_; 
lean_inc(v_r_1872_);
lean_inc(v_l_1871_);
lean_inc(v_v_1870_);
lean_inc(v_k_1869_);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_r_1855_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; lean_object* v_unused_1909_; 
v_unused_1905_ = lean_ctor_get(v_r_1855_, 4);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_r_1855_, 3);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_r_1855_, 2);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_r_1855_, 1);
lean_dec(v_unused_1908_);
v_unused_1909_ = lean_ctor_get(v_r_1855_, 0);
lean_dec(v_unused_1909_);
v___x_1877_ = v_r_1855_;
v_isShared_1878_ = v_isSharedCheck_1904_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v_r_1855_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1904_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___x_1892_; lean_object* v___y_1894_; 
v___x_1879_ = lean_nat_add(v___x_1849_, v_size_1851_);
lean_dec(v_size_1851_);
v___x_1880_ = lean_nat_add(v___x_1879_, v_size_1850_);
lean_dec(v___x_1879_);
v___x_1892_ = lean_nat_add(v___x_1849_, v_size_1867_);
if (lean_obj_tag(v_l_1871_) == 0)
{
lean_object* v_size_1902_; 
v_size_1902_ = lean_ctor_get(v_l_1871_, 0);
lean_inc(v_size_1902_);
v___y_1894_ = v_size_1902_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___y_1894_ = v___x_1903_;
goto v___jp_1893_;
}
v___jp_1881_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_nat_add(v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v_impl_1848_);
lean_ctor_set(v___x_1877_, 3, v_r_1872_);
lean_ctor_set(v___x_1877_, 2, v_v_1356_);
lean_ctor_set(v___x_1877_, 1, v_k_1355_);
lean_ctor_set(v___x_1877_, 0, v___x_1885_);
v___x_1887_ = v___x_1877_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_r_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_impl_1848_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 4, v___x_1887_);
lean_ctor_set(v___x_1865_, 3, v___y_1882_);
lean_ctor_set(v___x_1865_, 2, v_v_1870_);
lean_ctor_set(v___x_1865_, 1, v_k_1869_);
lean_ctor_set(v___x_1865_, 0, v___x_1880_);
v___x_1889_ = v___x_1865_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_k_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_v_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v___y_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
v___jp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_nat_add(v___x_1892_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec(v___x_1892_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_l_1871_);
lean_ctor_set(v___x_1360_, 3, v_l_1854_);
lean_ctor_set(v___x_1360_, 2, v_v_1853_);
lean_ctor_set(v___x_1360_, 1, v_k_1852_);
lean_ctor_set(v___x_1360_, 0, v___x_1895_);
v___x_1897_ = v___x_1360_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_k_1852_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_v_1853_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_l_1854_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_l_1871_);
v___x_1897_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_nat_add(v___x_1849_, v_size_1850_);
if (lean_obj_tag(v_r_1872_) == 0)
{
lean_object* v_size_1899_; 
v_size_1899_ = lean_ctor_get(v_r_1872_, 0);
lean_inc(v_size_1899_);
v___y_1882_ = v___x_1897_;
v___y_1883_ = v___x_1898_;
v___y_1884_ = v_size_1899_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___y_1882_ = v___x_1897_;
v___y_1883_ = v___x_1898_;
v___y_1884_ = v___x_1900_;
goto v___jp_1881_;
}
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_del_object(v___x_1360_);
v___x_1910_ = lean_nat_add(v___x_1849_, v_size_1851_);
lean_dec(v_size_1851_);
v___x_1911_ = lean_nat_add(v___x_1910_, v_size_1850_);
lean_dec(v___x_1910_);
v___x_1912_ = lean_nat_add(v___x_1849_, v_size_1850_);
v___x_1913_ = lean_nat_add(v___x_1912_, v_size_1868_);
lean_dec(v___x_1912_);
lean_inc_ref(v_impl_1848_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 4, v_impl_1848_);
lean_ctor_set(v___x_1865_, 3, v_r_1855_);
lean_ctor_set(v___x_1865_, 2, v_v_1356_);
lean_ctor_set(v___x_1865_, 1, v_k_1355_);
lean_ctor_set(v___x_1865_, 0, v___x_1913_);
v___x_1915_ = v___x_1865_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_r_1855_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_impl_1848_);
v___x_1915_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_isSharedCheck_1922_ = !lean_is_exclusive(v_impl_1848_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1923_ = lean_ctor_get(v_impl_1848_, 4);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_impl_1848_, 3);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_impl_1848_, 2);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_impl_1848_, 1);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_impl_1848_, 0);
lean_dec(v_unused_1927_);
v___x_1917_ = v_impl_1848_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v_impl_1848_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v___x_1915_);
lean_ctor_set(v___x_1917_, 3, v_l_1854_);
lean_ctor_set(v___x_1917_, 2, v_v_1853_);
lean_ctor_set(v___x_1917_, 1, v_k_1852_);
lean_ctor_set(v___x_1917_, 0, v___x_1911_);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1852_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1853_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_l_1854_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___x_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v_size_1935_ = lean_ctor_get(v_impl_1848_, 0);
v___x_1936_ = lean_nat_add(v___x_1849_, v_size_1935_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_impl_1848_);
lean_ctor_set(v___x_1360_, 0, v___x_1936_);
v___x_1938_ = v___x_1360_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_impl_1848_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
if (lean_obj_tag(v_l_1357_) == 0)
{
lean_object* v_l_1940_; 
v_l_1940_ = lean_ctor_get(v_l_1357_, 3);
if (lean_obj_tag(v_l_1940_) == 0)
{
lean_object* v_r_1941_; 
lean_inc_ref(v_l_1940_);
v_r_1941_ = lean_ctor_get(v_l_1357_, 4);
lean_inc(v_r_1941_);
if (lean_obj_tag(v_r_1941_) == 0)
{
lean_object* v_size_1942_; lean_object* v_k_1943_; lean_object* v_v_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1957_; 
v_size_1942_ = lean_ctor_get(v_l_1357_, 0);
v_k_1943_ = lean_ctor_get(v_l_1357_, 1);
v_v_1944_ = lean_ctor_get(v_l_1357_, 2);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; lean_object* v_unused_1959_; 
v_unused_1958_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1959_);
v___x_1946_ = v_l_1357_;
v_isShared_1947_ = v_isSharedCheck_1957_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_v_1944_);
lean_inc(v_k_1943_);
lean_inc(v_size_1942_);
lean_dec(v_l_1357_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1957_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_size_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_size_1948_ = lean_ctor_get(v_r_1941_, 0);
v___x_1949_ = lean_nat_add(v___x_1849_, v_size_1942_);
lean_dec(v_size_1942_);
v___x_1950_ = lean_nat_add(v___x_1849_, v_size_1948_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_impl_1848_);
lean_ctor_set(v___x_1946_, 3, v_r_1941_);
lean_ctor_set(v___x_1946_, 2, v_v_1356_);
lean_ctor_set(v___x_1946_, 1, v_k_1355_);
lean_ctor_set(v___x_1946_, 0, v___x_1950_);
v___x_1952_ = v___x_1946_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_r_1941_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_impl_1848_);
v___x_1952_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v___x_1952_);
lean_ctor_set(v___x_1360_, 3, v_l_1940_);
lean_ctor_set(v___x_1360_, 2, v_v_1944_);
lean_ctor_set(v___x_1360_, 1, v_k_1943_);
lean_ctor_set(v___x_1360_, 0, v___x_1949_);
v___x_1954_ = v___x_1360_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_k_1943_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_v_1944_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_l_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_k_1960_; lean_object* v_v_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1972_; 
v_k_1960_ = lean_ctor_get(v_l_1357_, 1);
v_v_1961_ = lean_ctor_get(v_l_1357_, 2);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; lean_object* v_unused_1974_; lean_object* v_unused_1975_; 
v_unused_1973_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1975_);
v___x_1963_ = v_l_1357_;
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_v_1961_);
lean_inc(v_k_1960_);
lean_dec(v_l_1357_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_unsigned_to_nat(3u);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 3, v_r_1941_);
lean_ctor_set(v___x_1963_, 2, v_v_1356_);
lean_ctor_set(v___x_1963_, 1, v_k_1355_);
lean_ctor_set(v___x_1963_, 0, v___x_1849_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_r_1941_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_r_1941_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v___x_1967_);
lean_ctor_set(v___x_1360_, 3, v_l_1940_);
lean_ctor_set(v___x_1360_, 2, v_v_1961_);
lean_ctor_set(v___x_1360_, 1, v_k_1960_);
lean_ctor_set(v___x_1360_, 0, v___x_1965_);
v___x_1969_ = v___x_1360_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_k_1960_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_v_1961_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_l_1940_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
else
{
lean_object* v_r_1976_; 
v_r_1976_ = lean_ctor_get(v_l_1357_, 4);
lean_inc(v_r_1976_);
if (lean_obj_tag(v_r_1976_) == 0)
{
lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2001_; 
lean_inc(v_l_1940_);
v_k_1977_ = lean_ctor_get(v_l_1357_, 1);
v_v_1978_ = lean_ctor_get(v_l_1357_, 2);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2002_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_2004_);
v___x_1980_ = v_l_1357_;
v_isShared_1981_ = v_isSharedCheck_2001_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_v_1978_);
lean_inc(v_k_1977_);
lean_dec(v_l_1357_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2001_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1997_; 
v_k_1982_ = lean_ctor_get(v_r_1976_, 1);
v_v_1983_ = lean_ctor_get(v_r_1976_, 2);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_r_1976_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; lean_object* v_unused_2000_; 
v_unused_1998_ = lean_ctor_get(v_r_1976_, 4);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_r_1976_, 3);
lean_dec(v_unused_1999_);
v_unused_2000_ = lean_ctor_get(v_r_1976_, 0);
lean_dec(v_unused_2000_);
v___x_1985_ = v_r_1976_;
v_isShared_1986_ = v_isSharedCheck_1997_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
lean_dec(v_r_1976_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1997_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1987_ = lean_unsigned_to_nat(3u);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v_l_1940_);
lean_ctor_set(v___x_1985_, 3, v_l_1940_);
lean_ctor_set(v___x_1985_, 2, v_v_1978_);
lean_ctor_set(v___x_1985_, 1, v_k_1977_);
lean_ctor_set(v___x_1985_, 0, v___x_1849_);
v___x_1989_ = v___x_1985_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_l_1940_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_l_1940_);
v___x_1989_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 4, v_l_1940_);
lean_ctor_set(v___x_1980_, 2, v_v_1356_);
lean_ctor_set(v___x_1980_, 1, v_k_1355_);
lean_ctor_set(v___x_1980_, 0, v___x_1849_);
v___x_1991_ = v___x_1980_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_l_1940_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_l_1940_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v___x_1991_);
lean_ctor_set(v___x_1360_, 3, v___x_1989_);
lean_ctor_set(v___x_1360_, 2, v_v_1983_);
lean_ctor_set(v___x_1360_, 1, v_k_1982_);
lean_ctor_set(v___x_1360_, 0, v___x_1987_);
v___x_1993_ = v___x_1360_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_unsigned_to_nat(2u);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_r_1976_);
lean_ctor_set(v___x_1360_, 0, v___x_2005_);
v___x_2007_ = v___x_1360_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_r_1976_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_object* v___x_2010_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 4, v_l_1357_);
lean_ctor_set(v___x_1360_, 0, v___x_1849_);
v___x_2010_ = v___x_1360_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_l_1357_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_l_1357_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
}
else
{
return v_t_1354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2014_, lean_object* v_t_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2014_, v_t_2015_);
lean_dec(v_k_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2017_, lean_object* v_v_2018_, lean_object* v_i_2019_){
_start:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_array_get_size(v_xs_2017_);
v___x_2021_ = lean_nat_dec_lt(v_i_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v_i_2019_);
v___x_2022_ = lean_box(0);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_array_fget_borrowed(v_xs_2017_, v_i_2019_);
v___x_2024_ = l_Lean_instBEqFVarId_beq(v___x_2023_, v_v_2018_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_add(v_i_2019_, v___x_2025_);
lean_dec(v_i_2019_);
v_i_2019_ = v___x_2026_;
goto _start;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_i_2019_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2029_, lean_object* v_v_2030_, lean_object* v_i_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2029_, v_v_2030_, v_i_2031_);
lean_dec(v_v_2030_);
lean_dec_ref(v_xs_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2033_, lean_object* v_v_2034_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2033_, v_v_2034_, v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2037_, lean_object* v_v_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2037_, v_v_2038_);
lean_dec(v_v_2038_);
lean_dec_ref(v_xs_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2040_, size_t v_x_2041_, lean_object* v_x_2042_){
_start:
{
if (lean_obj_tag(v_x_2040_) == 0)
{
lean_object* v_es_2043_; lean_object* v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; lean_object* v_j_2047_; lean_object* v_entry_2048_; 
v_es_2043_ = lean_ctor_get(v_x_2040_, 0);
v___x_2044_ = lean_box(2);
v___x_2045_ = ((size_t)31ULL);
v___x_2046_ = lean_usize_land(v_x_2041_, v___x_2045_);
v_j_2047_ = lean_usize_to_nat(v___x_2046_);
v_entry_2048_ = lean_array_get(v___x_2044_, v_es_2043_, v_j_2047_);
switch(lean_obj_tag(v_entry_2048_))
{
case 0:
{
lean_object* v_key_2049_; uint8_t v___x_2050_; 
v_key_2049_ = lean_ctor_get(v_entry_2048_, 0);
lean_inc(v_key_2049_);
lean_dec_ref_known(v_entry_2048_, 2);
v___x_2050_ = l_Lean_instBEqFVarId_beq(v_x_2042_, v_key_2049_);
lean_dec(v_key_2049_);
if (v___x_2050_ == 0)
{
lean_dec(v_j_2047_);
return v_x_2040_;
}
else
{
lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2058_; 
lean_inc_ref(v_es_2043_);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2040_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_x_2040_, 0);
lean_dec(v_unused_2059_);
v___x_2052_ = v_x_2040_;
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
else
{
lean_dec(v_x_2040_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_array_set(v_es_2043_, v_j_2047_, v___x_2044_);
lean_dec(v_j_2047_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
case 1:
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2094_; 
lean_inc_ref(v_es_2043_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2040_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_x_2040_, 0);
lean_dec(v_unused_2095_);
v___x_2061_ = v_x_2040_;
v_isShared_2062_ = v_isSharedCheck_2094_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_x_2040_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2094_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_node_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2093_; 
v_node_2063_ = lean_ctor_get(v_entry_2048_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_entry_2048_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2065_ = v_entry_2048_;
v_isShared_2066_ = v_isSharedCheck_2093_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_node_2063_);
lean_dec(v_entry_2048_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2093_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
size_t v___x_2067_; lean_object* v_entries_2068_; size_t v___x_2069_; lean_object* v_newNode_2070_; lean_object* v___x_2071_; 
v___x_2067_ = ((size_t)5ULL);
v_entries_2068_ = lean_array_set(v_es_2043_, v_j_2047_, v___x_2044_);
v___x_2069_ = lean_usize_shift_right(v_x_2041_, v___x_2067_);
v_newNode_2070_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2063_, v___x_2069_, v_x_2042_);
lean_inc_ref(v_newNode_2070_);
v___x_2071_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_newNode_2070_);
v___x_2073_ = v___x_2065_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_newNode_2070_);
v___x_2073_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = lean_array_set(v_entries_2068_, v_j_2047_, v___x_2073_);
lean_dec(v_j_2047_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2074_);
v___x_2076_ = v___x_2061_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v_val_2079_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_newNode_2070_);
lean_del_object(v___x_2065_);
v_val_2079_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2071_, 1);
v_fst_2080_ = lean_ctor_get(v_val_2079_, 0);
v_snd_2081_ = lean_ctor_get(v_val_2079_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_val_2079_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2083_ = v_val_2079_;
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_inc(v_fst_2080_);
lean_dec(v_val_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_fst_2080_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_snd_2081_);
v___x_2086_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_array_set(v_entries_2068_, v_j_2047_, v___x_2086_);
lean_dec(v_j_2047_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2087_);
v___x_2089_ = v___x_2061_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2047_);
return v_x_2040_;
}
}
}
else
{
lean_object* v_ks_2096_; lean_object* v_vs_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_ks_2096_ = lean_ctor_get(v_x_2040_, 0);
v_vs_2097_ = lean_ctor_get(v_x_2040_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2040_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2099_ = v_x_2040_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_vs_2097_);
lean_inc(v_ks_2096_);
lean_dec(v_x_2040_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2096_, v_x_2042_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v___x_2103_; 
if (v_isShared_2100_ == 0)
{
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_ks_2096_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_vs_2097_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
else
{
lean_object* v_val_2105_; lean_object* v_keys_x27_2106_; lean_object* v_vals_x27_2107_; lean_object* v___x_2109_; 
v_val_2105_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_n(v_val_2105_, 2);
lean_dec_ref_known(v___x_2101_, 1);
v_keys_x27_2106_ = l_Array_eraseIdx___redArg(v_ks_2096_, v_val_2105_);
v_vals_x27_2107_ = l_Array_eraseIdx___redArg(v_vs_2097_, v_val_2105_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_vals_x27_2107_);
lean_ctor_set(v___x_2099_, 0, v_keys_x27_2106_);
v___x_2109_ = v___x_2099_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_keys_x27_2106_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_vals_x27_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
size_t v_x_2640__boxed_2115_; lean_object* v_res_2116_; 
v_x_2640__boxed_2115_ = lean_unbox_usize(v_x_2113_);
lean_dec(v_x_2113_);
v_res_2116_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2112_, v_x_2640__boxed_2115_, v_x_2114_);
lean_dec(v_x_2114_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
uint64_t v___x_2119_; size_t v_h_2120_; lean_object* v___x_2121_; 
v___x_2119_ = l_Lean_instHashableFVarId_hash(v_x_2118_);
v_h_2120_ = lean_uint64_to_usize(v___x_2119_);
v___x_2121_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2117_, v_h_2120_, v_x_2118_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2122_, v_x_2123_);
lean_dec(v_x_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object* v_lctx_2125_, lean_object* v_fvarId_2126_){
_start:
{
lean_object* v_fvarIdToDecl_2127_; lean_object* v_decls_2128_; lean_object* v_auxDeclToFullName_2129_; lean_object* v___x_2130_; 
v_fvarIdToDecl_2127_ = lean_ctor_get(v_lctx_2125_, 0);
v_decls_2128_ = lean_ctor_get(v_lctx_2125_, 1);
v_auxDeclToFullName_2129_ = lean_ctor_get(v_lctx_2125_, 2);
v___x_2130_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2127_, v_fvarId_2126_);
if (lean_obj_tag(v___x_2130_) == 0)
{
return v_lctx_2125_;
}
else
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2150_; 
lean_inc(v_auxDeclToFullName_2129_);
lean_inc_ref(v_decls_2128_);
lean_inc_ref(v_fvarIdToDecl_2127_);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_lctx_2125_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2151_ = lean_ctor_get(v_lctx_2125_, 2);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_lctx_2125_, 1);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_lctx_2125_, 0);
lean_dec(v_unused_2153_);
v___x_2132_ = v_lctx_2125_;
v_isShared_2133_ = v_isSharedCheck_2150_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_lctx_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2150_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_val_2134_; lean_object* v___x_2135_; lean_object* v___y_2137_; lean_object* v_index_2149_; 
v_val_2134_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2134_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2135_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2127_, v_fvarId_2126_);
v_index_2149_ = lean_ctor_get(v_val_2134_, 0);
lean_inc(v_index_2149_);
v___y_2137_ = v_index_2149_;
goto v___jp_2136_;
v___jp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_PersistentArray_set___redArg(v_decls_2128_, v___y_2137_, v___x_2138_);
lean_dec(v___y_2137_);
v___x_2140_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2139_);
v___x_2141_ = l_Lean_LocalDecl_isAuxDecl(v_val_2134_);
lean_dec(v_val_2134_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2143_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v___x_2140_);
lean_ctor_set(v___x_2132_, 0, v___x_2135_);
v___x_2143_ = v___x_2132_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_auxDeclToFullName_2129_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2126_, v_auxDeclToFullName_2129_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 2, v___x_2145_);
lean_ctor_set(v___x_2132_, 1, v___x_2140_);
lean_ctor_set(v___x_2132_, 0, v___x_2135_);
v___x_2147_ = v___x_2132_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object* v_lctx_2154_, lean_object* v_fvarId_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_LocalContext_erase(v_lctx_2154_, v_fvarId_2155_);
lean_dec(v_fvarId_2155_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2158_, v_x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2161_, v_x_2162_, v_x_2163_);
lean_dec(v_x_2163_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2165_, lean_object* v_k_2166_, lean_object* v_t_2167_, lean_object* v_h_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2166_, v_t_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2170_, lean_object* v_k_2171_, lean_object* v_t_2172_, lean_object* v_h_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2170_, v_k_2171_, v_t_2172_, v_h_2173_);
lean_dec(v_k_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, size_t v_x_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2176_, v_x_2177_, v_x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
size_t v_x_2862__boxed_2184_; lean_object* v_res_2185_; 
v_x_2862__boxed_2184_ = lean_unbox_usize(v_x_2182_);
lean_dec(v_x_2182_);
v_res_2185_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2180_, v_x_2181_, v_x_2862__boxed_2184_, v_x_2183_);
lean_dec(v_x_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2186_){
_start:
{
lean_object* v_decls_2187_; lean_object* v_fvarIdToDecl_2188_; lean_object* v_auxDeclToFullName_2189_; lean_object* v_size_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_decls_2187_ = lean_ctor_get(v_lctx_2186_, 1);
v_fvarIdToDecl_2188_ = lean_ctor_get(v_lctx_2186_, 0);
v_auxDeclToFullName_2189_ = lean_ctor_get(v_lctx_2186_, 2);
v_size_2190_ = lean_ctor_get(v_decls_2187_, 2);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_eq(v_size_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v_size_2190_, v___x_2194_);
v___x_2196_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2193_, v_decls_2187_, v___x_2195_);
lean_dec(v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
return v_lctx_2186_;
}
else
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2215_; 
lean_inc(v_auxDeclToFullName_2189_);
lean_inc_ref(v_fvarIdToDecl_2188_);
lean_inc_ref(v_decls_2187_);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_lctx_2186_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; lean_object* v_unused_2217_; lean_object* v_unused_2218_; 
v_unused_2216_ = lean_ctor_get(v_lctx_2186_, 2);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_lctx_2186_, 1);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_lctx_2186_, 0);
lean_dec(v_unused_2218_);
v___x_2198_ = v_lctx_2186_;
v_isShared_2199_ = v_isSharedCheck_2215_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_lctx_2186_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2215_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_val_2200_; lean_object* v___y_2202_; lean_object* v_fvarId_2214_; 
v_val_2200_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2196_, 1);
v_fvarId_2214_ = lean_ctor_get(v_val_2200_, 1);
lean_inc(v_fvarId_2214_);
v___y_2202_ = v_fvarId_2214_;
goto v___jp_2201_;
v___jp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2203_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2188_, v___y_2202_);
v___x_2204_ = l_Lean_PersistentArray_pop___redArg(v_decls_2187_);
v___x_2205_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2204_);
v___x_2206_ = l_Lean_LocalDecl_isAuxDecl(v_val_2200_);
lean_dec(v_val_2200_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v___y_2202_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2205_);
lean_ctor_set(v___x_2198_, 0, v___x_2203_);
v___x_2208_ = v___x_2198_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_auxDeclToFullName_2189_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2202_, v_auxDeclToFullName_2189_);
lean_dec(v___y_2202_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 2, v___x_2210_);
lean_ctor_set(v___x_2198_, 1, v___x_2205_);
lean_ctor_set(v___x_2198_, 0, v___x_2203_);
v___x_2212_ = v___x_2198_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
else
{
return v_lctx_2186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2219_, lean_object* v_as_2220_, lean_object* v_i_2221_){
_start:
{
lean_object* v_zero_2222_; uint8_t v_isZero_2223_; 
v_zero_2222_ = lean_unsigned_to_nat(0u);
v_isZero_2223_ = lean_nat_dec_eq(v_i_2221_, v_zero_2222_);
if (v_isZero_2223_ == 1)
{
lean_object* v___x_2224_; 
lean_dec(v_i_2221_);
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_one_2225_; lean_object* v_n_2226_; lean_object* v___y_2228_; lean_object* v___x_2230_; lean_object* v___y_2232_; 
v_one_2225_ = lean_unsigned_to_nat(1u);
v_n_2226_ = lean_nat_sub(v_i_2221_, v_one_2225_);
lean_dec(v_i_2221_);
v___x_2230_ = lean_array_fget_borrowed(v_as_2220_, v_n_2226_);
if (lean_obj_tag(v___x_2230_) == 0)
{
v___y_2228_ = v___x_2230_;
goto v___jp_2227_;
}
else
{
lean_object* v_val_2235_; lean_object* v_userName_2236_; 
v_val_2235_ = lean_ctor_get(v___x_2230_, 0);
v_userName_2236_ = lean_ctor_get(v_val_2235_, 2);
v___y_2232_ = v_userName_2236_;
goto v___jp_2231_;
}
v___jp_2227_:
{
if (lean_obj_tag(v___y_2228_) == 0)
{
v_i_2221_ = v_n_2226_;
goto _start;
}
else
{
lean_dec(v_n_2226_);
lean_inc_ref(v___y_2228_);
return v___y_2228_;
}
}
v___jp_2231_:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_name_eq(v___y_2232_, v_userName_2219_);
if (v___x_2233_ == 0)
{
v_i_2221_ = v_n_2226_;
goto _start;
}
else
{
v___y_2228_ = v___x_2230_;
goto v___jp_2227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2237_, lean_object* v_as_2238_, lean_object* v_i_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2237_, v_as_2238_, v_i_2239_);
lean_dec_ref(v_as_2238_);
lean_dec(v_userName_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2241_, lean_object* v_as_2242_, lean_object* v_i_2243_){
_start:
{
lean_object* v_zero_2244_; uint8_t v_isZero_2245_; 
v_zero_2244_ = lean_unsigned_to_nat(0u);
v_isZero_2245_ = lean_nat_dec_eq(v_i_2243_, v_zero_2244_);
if (v_isZero_2245_ == 1)
{
lean_object* v___x_2246_; 
lean_dec(v_i_2243_);
v___x_2246_ = lean_box(0);
return v___x_2246_;
}
else
{
lean_object* v_one_2247_; lean_object* v_n_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_one_2247_ = lean_unsigned_to_nat(1u);
v_n_2248_ = lean_nat_sub(v_i_2243_, v_one_2247_);
lean_dec(v_i_2243_);
v___x_2249_ = lean_array_fget_borrowed(v_as_2242_, v_n_2248_);
v___x_2250_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2241_, v___x_2249_);
if (lean_obj_tag(v___x_2250_) == 0)
{
v_i_2243_ = v_n_2248_;
goto _start;
}
else
{
lean_dec(v_n_2248_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2252_, lean_object* v_x_2253_){
_start:
{
if (lean_obj_tag(v_x_2253_) == 0)
{
lean_object* v_cs_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_cs_2254_ = lean_ctor_get(v_x_2253_, 0);
v___x_2255_ = lean_array_get_size(v_cs_2254_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2252_, v_cs_2254_, v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v_vs_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_vs_2257_ = lean_ctor_get(v_x_2253_, 0);
v___x_2258_ = lean_array_get_size(v_vs_2257_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2252_, v_vs_2257_, v___x_2258_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2260_, v_x_2261_);
lean_dec_ref(v_x_2261_);
lean_dec(v_userName_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2263_, lean_object* v_as_2264_, lean_object* v_i_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2263_, v_as_2264_, v_i_2265_);
lean_dec_ref(v_as_2264_);
lean_dec(v_userName_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2267_, lean_object* v_t_2268_){
_start:
{
lean_object* v_root_2269_; lean_object* v_tail_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_root_2269_ = lean_ctor_get(v_t_2268_, 0);
v_tail_2270_ = lean_ctor_get(v_t_2268_, 1);
v___x_2271_ = lean_array_get_size(v_tail_2270_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2267_, v_tail_2270_, v___x_2271_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2267_, v_root_2269_);
return v___x_2273_;
}
else
{
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2274_, lean_object* v_t_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2274_, v_t_2275_);
lean_dec_ref(v_t_2275_);
lean_dec(v_userName_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2277_, lean_object* v_userName_2278_){
_start:
{
lean_object* v_decls_2279_; lean_object* v___x_2280_; 
v_decls_2279_ = lean_ctor_get(v_lctx_2277_, 1);
v___x_2280_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2278_, v_decls_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2281_, lean_object* v_userName_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2281_, v_userName_2282_);
lean_dec(v_userName_2282_);
lean_dec_ref(v_lctx_2281_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2284_, lean_object* v_as_2285_, lean_object* v_i_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2284_, v_as_2285_, v_i_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2289_, lean_object* v_as_2290_, lean_object* v_i_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2289_, v_as_2290_, v_i_2291_, v_a_2292_);
lean_dec_ref(v_as_2290_);
lean_dec(v_userName_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2294_, lean_object* v_as_2295_, lean_object* v_i_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2294_, v_as_2295_, v_i_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2299_, lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2299_, v_as_2300_, v_i_2301_, v_a_2302_);
lean_dec_ref(v_as_2300_);
lean_dec(v_userName_2299_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2307_, lean_object* v_userName_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2307_, v_userName_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2310_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2311_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2312_ = lean_unsigned_to_nat(412u);
v___x_2313_ = lean_unsigned_to_nat(17u);
v___x_2314_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2315_ = 1;
v___x_2316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2308_, v___x_2315_);
v___x_2317_ = lean_string_append(v___x_2314_, v___x_2316_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2319_ = lean_string_append(v___x_2317_, v___x_2318_);
v___x_2320_ = l_mkPanicMessageWithDecl(v___x_2310_, v___x_2311_, v___x_2312_, v___x_2313_, v___x_2319_);
lean_dec_ref(v___x_2319_);
v___x_2321_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v_val_2322_; 
lean_dec(v_userName_2308_);
v_val_2322_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2309_, 1);
return v_val_2322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2323_, lean_object* v_userName_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2323_, v_userName_2324_);
lean_dec_ref(v_lctx_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2326_, lean_object* v_userName_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2326_, v_userName_2327_);
if (lean_obj_tag(v___x_2328_) == 0)
{
uint8_t v___x_2329_; 
v___x_2329_ = 0;
return v___x_2329_;
}
else
{
uint8_t v___x_2330_; 
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = 1;
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2331_, lean_object* v_userName_2332_){
_start:
{
uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_res_2333_ = l_Lean_LocalContext_usesUserName(v_lctx_2331_, v_userName_2332_);
lean_dec(v_userName_2332_);
lean_dec_ref(v_lctx_2331_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2335_, lean_object* v_suggestion_2336_, lean_object* v_i_2337_){
_start:
{
lean_object* v_curr_2338_; uint8_t v___x_2339_; 
lean_inc(v_i_2337_);
lean_inc(v_suggestion_2336_);
v_curr_2338_ = lean_name_append_index_after(v_suggestion_2336_, v_i_2337_);
v___x_2339_ = l_Lean_LocalContext_usesUserName(v_lctx_2335_, v_curr_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v_suggestion_2336_);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_nat_add(v_i_2337_, v___x_2340_);
lean_dec(v_i_2337_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_curr_2338_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec(v_curr_2338_);
v___x_2343_ = lean_unsigned_to_nat(1u);
v___x_2344_ = lean_nat_add(v_i_2337_, v___x_2343_);
lean_dec(v_i_2337_);
v_i_2337_ = v___x_2344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2346_, lean_object* v_suggestion_2347_, lean_object* v_i_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2346_, v_suggestion_2347_, v_i_2348_);
lean_dec_ref(v_lctx_2346_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2350_, lean_object* v_suggestion_2351_){
_start:
{
lean_object* v_suggestion_2352_; uint8_t v___x_2353_; 
v_suggestion_2352_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2351_);
v___x_2353_ = l_Lean_LocalContext_usesUserName(v_lctx_2350_, v_suggestion_2352_);
if (v___x_2353_ == 0)
{
return v_suggestion_2352_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v_fst_2356_; 
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2350_, v_suggestion_2352_, v___x_2354_);
v_fst_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_fst_2356_);
lean_dec_ref(v___x_2355_);
return v_fst_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2357_, lean_object* v_suggestion_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_LocalContext_getUnusedName(v_lctx_2357_, v_suggestion_2358_);
lean_dec(v_suggestion_2358_);
lean_dec_ref(v_lctx_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2360_){
_start:
{
lean_object* v_decls_2361_; lean_object* v_size_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v_decls_2361_ = lean_ctor_get(v_lctx_2360_, 1);
v_size_2362_ = lean_ctor_get(v_decls_2361_, 2);
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_sub(v_size_2362_, v___x_2364_);
v___x_2366_ = lean_nat_dec_lt(v___x_2365_, v_size_2362_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; 
lean_dec(v___x_2365_);
v___x_2367_ = l_outOfBounds___redArg(v___x_2363_);
return v___x_2367_;
}
else
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2363_, v_decls_2361_, v___x_2365_);
lean_dec(v___x_2365_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_LocalContext_lastDecl(v_lctx_2369_);
lean_dec_ref(v_lctx_2369_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2371_, lean_object* v_fvarId_2372_, lean_object* v_userName_2373_){
_start:
{
lean_object* v_fvarIdToDecl_2374_; lean_object* v_decls_2375_; lean_object* v_auxDeclToFullName_2376_; lean_object* v_decl_2377_; lean_object* v_decl_2378_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2386_; lean_object* v_fvarId_2389_; 
v_fvarIdToDecl_2374_ = lean_ctor_get(v_lctx_2371_, 0);
lean_inc_ref(v_fvarIdToDecl_2374_);
v_decls_2375_ = lean_ctor_get(v_lctx_2371_, 1);
lean_inc_ref(v_decls_2375_);
v_auxDeclToFullName_2376_ = lean_ctor_get(v_lctx_2371_, 2);
lean_inc(v_auxDeclToFullName_2376_);
v_decl_2377_ = l_Lean_LocalContext_get_x21(v_lctx_2371_, v_fvarId_2372_);
v_decl_2378_ = l_Lean_LocalDecl_setUserName(v_decl_2377_, v_userName_2373_);
v_fvarId_2389_ = lean_ctor_get(v_decl_2378_, 1);
lean_inc(v_fvarId_2389_);
v___y_2386_ = v_fvarId_2389_;
goto v___jp_2385_;
v___jp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_decl_2378_);
v___x_2383_ = l_Lean_PersistentArray_set___redArg(v_decls_2375_, v___y_2381_, v___x_2382_);
lean_dec(v___y_2381_);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v___y_2380_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_ctor_set(v___x_2384_, 2, v_auxDeclToFullName_2376_);
return v___x_2384_;
}
v___jp_2385_:
{
lean_object* v___x_2387_; lean_object* v_index_2388_; 
lean_inc_ref(v_decl_2378_);
v___x_2387_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2374_, v___y_2386_, v_decl_2378_);
v_index_2388_ = lean_ctor_get(v_decl_2378_, 0);
lean_inc(v_index_2388_);
v___y_2380_ = v___x_2387_;
v___y_2381_ = v_index_2388_;
goto v___jp_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2390_, lean_object* v_fromName_2391_, lean_object* v_toName_2392_){
_start:
{
lean_object* v_fvarIdToDecl_2393_; lean_object* v_decls_2394_; lean_object* v_auxDeclToFullName_2395_; lean_object* v___x_2396_; 
v_fvarIdToDecl_2393_ = lean_ctor_get(v_lctx_2390_, 0);
v_decls_2394_ = lean_ctor_get(v_lctx_2390_, 1);
v_auxDeclToFullName_2395_ = lean_ctor_get(v_lctx_2390_, 2);
v___x_2396_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2390_, v_fromName_2391_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_dec(v_toName_2392_);
return v_lctx_2390_;
}
else
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2421_; 
lean_inc(v_auxDeclToFullName_2395_);
lean_inc_ref(v_decls_2394_);
lean_inc_ref(v_fvarIdToDecl_2393_);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_lctx_2390_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2422_ = lean_ctor_get(v_lctx_2390_, 2);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_lctx_2390_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_lctx_2390_, 0);
lean_dec(v_unused_2424_);
v___x_2398_ = v_lctx_2390_;
v_isShared_2399_ = v_isSharedCheck_2421_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v_lctx_2390_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2421_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2420_; 
v_val_2400_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2402_ = v___x_2396_;
v_isShared_2403_ = v_isSharedCheck_2420_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v___x_2396_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2420_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v_decl_2404_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2416_; lean_object* v_fvarId_2419_; 
v_decl_2404_ = l_Lean_LocalDecl_setUserName(v_val_2400_, v_toName_2392_);
v_fvarId_2419_ = lean_ctor_get(v_decl_2404_, 1);
lean_inc(v_fvarId_2419_);
v___y_2416_ = v_fvarId_2419_;
goto v___jp_2415_;
v___jp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v_decl_2404_);
v___x_2409_ = v___x_2402_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_decl_2404_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Lean_PersistentArray_set___redArg(v_decls_2394_, v___y_2407_, v___x_2409_);
lean_dec(v___y_2407_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v___x_2410_);
lean_ctor_set(v___x_2398_, 0, v___y_2406_);
v___x_2412_ = v___x_2398_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___y_2406_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_auxDeclToFullName_2395_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
v___jp_2415_:
{
lean_object* v___x_2417_; lean_object* v_index_2418_; 
lean_inc_ref(v_decl_2404_);
v___x_2417_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2393_, v___y_2416_, v_decl_2404_);
v_index_2418_ = lean_ctor_get(v_decl_2404_, 0);
lean_inc(v_index_2418_);
v___y_2406_ = v___x_2417_;
v___y_2407_ = v_index_2418_;
goto v___jp_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2425_, lean_object* v_fromName_2426_, lean_object* v_toName_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_LocalContext_renameUserName(v_lctx_2425_, v_fromName_2426_, v_toName_2427_);
lean_dec(v_fromName_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2431_, lean_object* v_fvarId_2432_, lean_object* v_f_2433_){
_start:
{
lean_object* v_fvarIdToDecl_2434_; lean_object* v_decls_2435_; lean_object* v_auxDeclToFullName_2436_; lean_object* v___x_2437_; 
v_fvarIdToDecl_2434_ = lean_ctor_get(v_lctx_2431_, 0);
v_decls_2435_ = lean_ctor_get(v_lctx_2431_, 1);
v_auxDeclToFullName_2436_ = lean_ctor_get(v_lctx_2431_, 2);
lean_inc_ref(v_lctx_2431_);
v___x_2437_ = lean_local_ctx_find(v_lctx_2431_, v_fvarId_2432_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_dec_ref(v_f_2433_);
return v_lctx_2431_;
}
else
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2464_; 
lean_inc(v_auxDeclToFullName_2436_);
lean_inc_ref(v_decls_2435_);
lean_inc_ref(v_fvarIdToDecl_2434_);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_lctx_2431_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; lean_object* v_unused_2466_; lean_object* v_unused_2467_; 
v_unused_2465_ = lean_ctor_get(v_lctx_2431_, 2);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_lctx_2431_, 1);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v_lctx_2431_, 0);
lean_dec(v_unused_2467_);
v___x_2439_ = v_lctx_2431_;
v_isShared_2440_ = v_isSharedCheck_2464_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v_lctx_2431_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2464_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_val_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2463_; 
v_val_2441_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2443_ = v___x_2437_;
v_isShared_2444_ = v_isSharedCheck_2463_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_val_2441_);
lean_dec(v___x_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2463_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_decl_2447_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2459_; lean_object* v_fvarId_2462_; 
v___x_2445_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2446_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2447_ = lean_apply_1(v_f_2433_, v_val_2441_);
v_fvarId_2462_ = lean_ctor_get(v_decl_2447_, 1);
lean_inc(v_fvarId_2462_);
v___y_2459_ = v_fvarId_2462_;
goto v___jp_2458_;
v___jp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v_decl_2447_);
v___x_2452_ = v___x_2443_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_decl_2447_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_PersistentArray_set___redArg(v_decls_2435_, v___y_2450_, v___x_2452_);
lean_dec(v___y_2450_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2453_);
lean_ctor_set(v___x_2439_, 0, v___y_2449_);
v___x_2455_ = v___x_2439_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___y_2449_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_auxDeclToFullName_2436_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v_index_2461_; 
lean_inc_ref(v_decl_2447_);
v___x_2460_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2445_, v___x_2446_, v_fvarIdToDecl_2434_, v___y_2459_, v_decl_2447_);
v_index_2461_ = lean_ctor_get(v_decl_2447_, 0);
lean_inc(v_index_2461_);
v___y_2449_ = v___x_2460_;
v___y_2450_ = v_index_2461_;
goto v___jp_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2468_, lean_object* v_as_2469_, size_t v_i_2470_, size_t v_stop_2471_, lean_object* v_b_2472_){
_start:
{
lean_object* v___y_2474_; uint8_t v___x_2478_; 
v___x_2478_ = lean_usize_dec_eq(v_i_2470_, v_stop_2471_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_array_uget(v_as_2469_, v_i_2470_);
if (lean_obj_tag(v___x_2479_) == 0)
{
v___y_2474_ = v_b_2472_;
goto v___jp_2473_;
}
else
{
lean_object* v_val_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2507_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2507_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_val_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2507_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_fvarIdToDecl_2484_; lean_object* v_decls_2485_; lean_object* v_auxDeclToFullName_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2506_; 
v_fvarIdToDecl_2484_ = lean_ctor_get(v_b_2472_, 0);
v_decls_2485_ = lean_ctor_get(v_b_2472_, 1);
v_auxDeclToFullName_2486_ = lean_ctor_get(v_b_2472_, 2);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_b_2472_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2488_ = v_b_2472_;
v_isShared_2489_ = v_isSharedCheck_2506_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_auxDeclToFullName_2486_);
lean_inc(v_decls_2485_);
lean_inc(v_fvarIdToDecl_2484_);
lean_dec(v_b_2472_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2506_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_decl_2490_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2502_; lean_object* v_fvarId_2505_; 
lean_inc_ref(v_f_2468_);
v_decl_2490_ = lean_apply_1(v_f_2468_, v_val_2480_);
v_fvarId_2505_ = lean_ctor_get(v_decl_2490_, 1);
lean_inc(v_fvarId_2505_);
v___y_2502_ = v_fvarId_2505_;
goto v___jp_2501_;
v___jp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v_decl_2490_);
v___x_2495_ = v___x_2482_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_decl_2490_);
v___x_2495_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = l_Lean_PersistentArray_set___redArg(v_decls_2485_, v___y_2493_, v___x_2495_);
lean_dec(v___y_2493_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2496_);
lean_ctor_set(v___x_2488_, 0, v___y_2492_);
v___x_2498_ = v___x_2488_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___y_2492_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_auxDeclToFullName_2486_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
v___y_2474_ = v___x_2498_;
goto v___jp_2473_;
}
}
}
v___jp_2501_:
{
lean_object* v___x_2503_; lean_object* v_index_2504_; 
lean_inc_ref(v_decl_2490_);
v___x_2503_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2484_, v___y_2502_, v_decl_2490_);
v_index_2504_ = lean_ctor_get(v_decl_2490_, 0);
lean_inc(v_index_2504_);
v___y_2492_ = v___x_2503_;
v___y_2493_ = v_index_2504_;
goto v___jp_2491_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2468_);
return v_b_2472_;
}
v___jp_2473_:
{
size_t v___x_2475_; size_t v___x_2476_; 
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2470_, v___x_2475_);
v_i_2470_ = v___x_2476_;
v_b_2472_ = v___y_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2508_, lean_object* v_as_2509_, lean_object* v_i_2510_, lean_object* v_stop_2511_, lean_object* v_b_2512_){
_start:
{
size_t v_i_boxed_2513_; size_t v_stop_boxed_2514_; lean_object* v_res_2515_; 
v_i_boxed_2513_ = lean_unbox_usize(v_i_2510_);
lean_dec(v_i_2510_);
v_stop_boxed_2514_ = lean_unbox_usize(v_stop_2511_);
lean_dec(v_stop_2511_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2508_, v_as_2509_, v_i_boxed_2513_, v_stop_boxed_2514_, v_b_2512_);
lean_dec_ref(v_as_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2516_, lean_object* v_x_2517_, lean_object* v_x_2518_){
_start:
{
if (lean_obj_tag(v_x_2517_) == 0)
{
lean_object* v_cs_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_cs_2519_ = lean_ctor_get(v_x_2517_, 0);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_cs_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec_ref(v_f_2516_);
return v_x_2518_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2521_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2516_, v_cs_2519_, v___x_2523_, v___x_2524_, v_x_2518_);
return v___x_2525_;
}
}
else
{
lean_object* v_vs_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_vs_2526_ = lean_ctor_get(v_x_2517_, 0);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_array_get_size(v_vs_2526_);
v___x_2529_ = lean_nat_dec_lt(v___x_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_dec_ref(v_f_2516_);
return v_x_2518_;
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2528_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2516_, v_vs_2526_, v___x_2530_, v___x_2531_, v_x_2518_);
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2533_, lean_object* v_as_2534_, size_t v_i_2535_, size_t v_stop_2536_, lean_object* v_b_2537_){
_start:
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_usize_dec_eq(v_i_2535_, v_stop_2536_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; size_t v___x_2541_; size_t v___x_2542_; 
v___x_2539_ = lean_array_uget_borrowed(v_as_2534_, v_i_2535_);
lean_inc_ref(v_f_2533_);
v___x_2540_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2533_, v___x_2539_, v_b_2537_);
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_add(v_i_2535_, v___x_2541_);
v_i_2535_ = v___x_2542_;
v_b_2537_ = v___x_2540_;
goto _start;
}
else
{
lean_dec_ref(v_f_2533_);
return v_b_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2544_, lean_object* v_as_2545_, lean_object* v_i_2546_, lean_object* v_stop_2547_, lean_object* v_b_2548_){
_start:
{
size_t v_i_boxed_2549_; size_t v_stop_boxed_2550_; lean_object* v_res_2551_; 
v_i_boxed_2549_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_stop_boxed_2550_ = lean_unbox_usize(v_stop_2547_);
lean_dec(v_stop_2547_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2544_, v_as_2545_, v_i_boxed_2549_, v_stop_boxed_2550_, v_b_2548_);
lean_dec_ref(v_as_2545_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2552_, v_x_2553_, v_x_2554_);
lean_dec_ref(v_x_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2556_, lean_object* v_x_2557_, size_t v_x_2558_, size_t v_x_2559_, lean_object* v_x_2560_){
_start:
{
if (lean_obj_tag(v_x_2557_) == 0)
{
lean_object* v_cs_2561_; lean_object* v___x_2562_; size_t v___x_2563_; lean_object* v_j_2564_; lean_object* v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_cs_2561_ = lean_ctor_get(v_x_2557_, 0);
v___x_2562_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2563_ = lean_usize_shift_right(v_x_2558_, v_x_2559_);
v_j_2564_ = lean_usize_to_nat(v___x_2563_);
v___x_2565_ = lean_array_get_borrowed(v___x_2562_, v_cs_2561_, v_j_2564_);
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_shift_left(v___x_2566_, v_x_2559_);
v___x_2568_ = lean_usize_sub(v___x_2567_, v___x_2566_);
v___x_2569_ = lean_usize_land(v_x_2558_, v___x_2568_);
v___x_2570_ = ((size_t)5ULL);
v___x_2571_ = lean_usize_sub(v_x_2559_, v___x_2570_);
lean_inc_ref(v_f_2556_);
v___x_2572_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2556_, v___x_2565_, v___x_2569_, v___x_2571_, v_x_2560_);
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_add(v_j_2564_, v___x_2573_);
lean_dec(v_j_2564_);
v___x_2575_ = lean_array_get_size(v_cs_2561_);
v___x_2576_ = lean_nat_dec_lt(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_dec(v___x_2574_);
lean_dec_ref(v_f_2556_);
return v___x_2572_;
}
else
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_usize_of_nat(v___x_2574_);
lean_dec(v___x_2574_);
v___x_2578_ = lean_usize_of_nat(v___x_2575_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2556_, v_cs_2561_, v___x_2577_, v___x_2578_, v___x_2572_);
return v___x_2579_;
}
}
else
{
lean_object* v_vs_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_vs_2580_ = lean_ctor_get(v_x_2557_, 0);
v___x_2581_ = lean_usize_to_nat(v_x_2558_);
v___x_2582_ = lean_array_get_size(v_vs_2580_);
v___x_2583_ = lean_nat_dec_lt(v___x_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_dec(v___x_2581_);
lean_dec_ref(v_f_2556_);
return v_x_2560_;
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_usize_of_nat(v___x_2581_);
lean_dec(v___x_2581_);
v___x_2585_ = lean_usize_of_nat(v___x_2582_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2556_, v_vs_2580_, v___x_2584_, v___x_2585_, v_x_2560_);
return v___x_2586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
size_t v_x_1489__boxed_2592_; size_t v_x_1490__boxed_2593_; lean_object* v_res_2594_; 
v_x_1489__boxed_2592_ = lean_unbox_usize(v_x_2589_);
lean_dec(v_x_2589_);
v_x_1490__boxed_2593_ = lean_unbox_usize(v_x_2590_);
lean_dec(v_x_2590_);
v_res_2594_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2587_, v_x_2588_, v_x_1489__boxed_2592_, v_x_1490__boxed_2593_, v_x_2591_);
lean_dec_ref(v_x_2588_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2595_, lean_object* v_t_2596_, lean_object* v_init_2597_, lean_object* v_start_2598_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_nat_dec_eq(v_start_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v_root_2601_; lean_object* v_tail_2602_; size_t v_shift_2603_; lean_object* v_tailOff_2604_; uint8_t v___x_2605_; 
v_root_2601_ = lean_ctor_get(v_t_2596_, 0);
v_tail_2602_ = lean_ctor_get(v_t_2596_, 1);
v_shift_2603_ = lean_ctor_get_usize(v_t_2596_, 4);
v_tailOff_2604_ = lean_ctor_get(v_t_2596_, 3);
v___x_2605_ = lean_nat_dec_le(v_tailOff_2604_, v_start_2598_);
if (v___x_2605_ == 0)
{
size_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = lean_usize_of_nat(v_start_2598_);
lean_inc_ref(v_f_2595_);
v___x_2607_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2595_, v_root_2601_, v___x_2606_, v_shift_2603_, v_init_2597_);
v___x_2608_ = lean_array_get_size(v_tail_2602_);
v___x_2609_ = lean_nat_dec_lt(v___x_2599_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_dec_ref(v_f_2595_);
return v___x_2607_;
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = lean_usize_of_nat(v___x_2608_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2595_, v_tail_2602_, v___x_2610_, v___x_2611_, v___x_2607_);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_nat_sub(v_start_2598_, v_tailOff_2604_);
v___x_2614_ = lean_array_get_size(v_tail_2602_);
v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_dec(v___x_2613_);
lean_dec_ref(v_f_2595_);
return v_init_2597_;
}
else
{
size_t v___x_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_usize_of_nat(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2617_ = lean_usize_of_nat(v___x_2614_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2595_, v_tail_2602_, v___x_2616_, v___x_2617_, v_init_2597_);
return v___x_2618_;
}
}
}
else
{
lean_object* v_root_2619_; lean_object* v_tail_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_root_2619_ = lean_ctor_get(v_t_2596_, 0);
v_tail_2620_ = lean_ctor_get(v_t_2596_, 1);
lean_inc_ref(v_f_2595_);
v___x_2621_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2595_, v_root_2619_, v_init_2597_);
v___x_2622_ = lean_array_get_size(v_tail_2620_);
v___x_2623_ = lean_nat_dec_lt(v___x_2599_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_dec_ref(v_f_2595_);
return v___x_2621_;
}
else
{
size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = lean_usize_of_nat(v___x_2622_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2595_, v_tail_2620_, v___x_2624_, v___x_2625_, v___x_2621_);
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2627_, lean_object* v_t_2628_, lean_object* v_init_2629_, lean_object* v_start_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2627_, v_t_2628_, v_init_2629_, v_start_2630_);
lean_dec(v_start_2630_);
lean_dec_ref(v_t_2628_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2632_, lean_object* v_f_2633_){
_start:
{
lean_object* v_decls_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_decls_2634_ = lean_ctor_get(v_lctx_2632_, 1);
lean_inc_ref(v_decls_2634_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2633_, v_decls_2634_, v_lctx_2632_, v___x_2635_);
lean_dec_ref(v_decls_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2637_, lean_object* v_fvarId_2638_, uint8_t v_kind_2639_){
_start:
{
lean_object* v_fvarIdToDecl_2640_; lean_object* v_decls_2641_; lean_object* v_auxDeclToFullName_2642_; lean_object* v___x_2643_; 
v_fvarIdToDecl_2640_ = lean_ctor_get(v_lctx_2637_, 0);
v_decls_2641_ = lean_ctor_get(v_lctx_2637_, 1);
v_auxDeclToFullName_2642_ = lean_ctor_get(v_lctx_2637_, 2);
lean_inc_ref(v_lctx_2637_);
v___x_2643_ = lean_local_ctx_find(v_lctx_2637_, v_fvarId_2638_);
if (lean_obj_tag(v___x_2643_) == 0)
{
return v_lctx_2637_;
}
else
{
lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2668_; 
lean_inc(v_auxDeclToFullName_2642_);
lean_inc_ref(v_decls_2641_);
lean_inc_ref(v_fvarIdToDecl_2640_);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_lctx_2637_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; lean_object* v_unused_2670_; lean_object* v_unused_2671_; 
v_unused_2669_ = lean_ctor_get(v_lctx_2637_, 2);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_lctx_2637_, 1);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_lctx_2637_, 0);
lean_dec(v_unused_2671_);
v___x_2645_ = v_lctx_2637_;
v_isShared_2646_ = v_isSharedCheck_2668_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v_lctx_2637_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2668_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_val_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2667_; 
v_val_2647_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2649_ = v___x_2643_;
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_val_2647_);
lean_dec(v___x_2643_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_decl_2651_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2663_; lean_object* v_fvarId_2666_; 
v_decl_2651_ = l_Lean_LocalDecl_setKind(v_val_2647_, v_kind_2639_);
v_fvarId_2666_ = lean_ctor_get(v_decl_2651_, 1);
lean_inc(v_fvarId_2666_);
v___y_2663_ = v_fvarId_2666_;
goto v___jp_2662_;
v___jp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v_decl_2651_);
v___x_2656_ = v___x_2649_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_decl_2651_);
v___x_2656_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = l_Lean_PersistentArray_set___redArg(v_decls_2641_, v___y_2654_, v___x_2656_);
lean_dec(v___y_2654_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2657_);
lean_ctor_set(v___x_2645_, 0, v___y_2653_);
v___x_2659_ = v___x_2645_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___y_2653_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_auxDeclToFullName_2642_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v_index_2665_; 
lean_inc_ref(v_decl_2651_);
v___x_2664_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2640_, v___y_2663_, v_decl_2651_);
v_index_2665_ = lean_ctor_get(v_decl_2651_, 0);
lean_inc(v_index_2665_);
v___y_2653_ = v___x_2664_;
v___y_2654_ = v_index_2665_;
goto v___jp_2652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2672_, lean_object* v_fvarId_2673_, lean_object* v_kind_2674_){
_start:
{
uint8_t v_kind_boxed_2675_; lean_object* v_res_2676_; 
v_kind_boxed_2675_ = lean_unbox(v_kind_2674_);
v_res_2676_ = l_Lean_LocalContext_setKind(v_lctx_2672_, v_fvarId_2673_, v_kind_boxed_2675_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2677_, lean_object* v_fvarId_2678_, uint8_t v_bi_2679_){
_start:
{
lean_object* v_fvarIdToDecl_2680_; lean_object* v_decls_2681_; lean_object* v_auxDeclToFullName_2682_; lean_object* v___x_2683_; 
v_fvarIdToDecl_2680_ = lean_ctor_get(v_lctx_2677_, 0);
v_decls_2681_ = lean_ctor_get(v_lctx_2677_, 1);
v_auxDeclToFullName_2682_ = lean_ctor_get(v_lctx_2677_, 2);
lean_inc_ref(v_lctx_2677_);
v___x_2683_ = lean_local_ctx_find(v_lctx_2677_, v_fvarId_2678_);
if (lean_obj_tag(v___x_2683_) == 0)
{
return v_lctx_2677_;
}
else
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2708_; 
lean_inc(v_auxDeclToFullName_2682_);
lean_inc_ref(v_decls_2681_);
lean_inc_ref(v_fvarIdToDecl_2680_);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_lctx_2677_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; 
v_unused_2709_ = lean_ctor_get(v_lctx_2677_, 2);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_lctx_2677_, 1);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_lctx_2677_, 0);
lean_dec(v_unused_2711_);
v___x_2685_ = v_lctx_2677_;
v_isShared_2686_ = v_isSharedCheck_2708_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_lctx_2677_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2708_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_val_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2707_; 
v_val_2687_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2689_ = v___x_2683_;
v_isShared_2690_ = v_isSharedCheck_2707_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_val_2687_);
lean_dec(v___x_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2707_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_decl_2691_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2703_; lean_object* v_fvarId_2706_; 
v_decl_2691_ = l_Lean_LocalDecl_setBinderInfo(v_val_2687_, v_bi_2679_);
v_fvarId_2706_ = lean_ctor_get(v_decl_2691_, 1);
lean_inc(v_fvarId_2706_);
v___y_2703_ = v_fvarId_2706_;
goto v___jp_2702_;
v___jp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v_decl_2691_);
v___x_2696_ = v___x_2689_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_decl_2691_);
v___x_2696_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = l_Lean_PersistentArray_set___redArg(v_decls_2681_, v___y_2694_, v___x_2696_);
lean_dec(v___y_2694_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2697_);
lean_ctor_set(v___x_2685_, 0, v___y_2693_);
v___x_2699_ = v___x_2685_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___y_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_auxDeclToFullName_2682_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v_index_2705_; 
lean_inc_ref(v_decl_2691_);
v___x_2704_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2680_, v___y_2703_, v_decl_2691_);
v_index_2705_ = lean_ctor_get(v_decl_2691_, 0);
lean_inc(v_index_2705_);
v___y_2693_ = v___x_2704_;
v___y_2694_ = v_index_2705_;
goto v___jp_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2712_, lean_object* v_fvarId_2713_, lean_object* v_bi_2714_){
_start:
{
uint8_t v_bi_boxed_2715_; lean_object* v_res_2716_; 
v_bi_boxed_2715_ = lean_unbox(v_bi_2714_);
v_res_2716_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2712_, v_fvarId_2713_, v_bi_boxed_2715_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2717_, lean_object* v_fvarId_2718_, lean_object* v_type_2719_){
_start:
{
lean_object* v_fvarIdToDecl_2720_; lean_object* v_decls_2721_; lean_object* v_auxDeclToFullName_2722_; lean_object* v___x_2723_; 
v_fvarIdToDecl_2720_ = lean_ctor_get(v_lctx_2717_, 0);
v_decls_2721_ = lean_ctor_get(v_lctx_2717_, 1);
v_auxDeclToFullName_2722_ = lean_ctor_get(v_lctx_2717_, 2);
lean_inc_ref(v_lctx_2717_);
v___x_2723_ = lean_local_ctx_find(v_lctx_2717_, v_fvarId_2718_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_dec_ref(v_type_2719_);
return v_lctx_2717_;
}
else
{
lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2748_; 
lean_inc(v_auxDeclToFullName_2722_);
lean_inc_ref(v_decls_2721_);
lean_inc_ref(v_fvarIdToDecl_2720_);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_lctx_2717_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; 
v_unused_2749_ = lean_ctor_get(v_lctx_2717_, 2);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_lctx_2717_, 1);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_lctx_2717_, 0);
lean_dec(v_unused_2751_);
v___x_2725_ = v_lctx_2717_;
v_isShared_2726_ = v_isSharedCheck_2748_;
goto v_resetjp_2724_;
}
else
{
lean_dec(v_lctx_2717_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2748_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_val_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2747_; 
v_val_2727_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2729_ = v___x_2723_;
v_isShared_2730_ = v_isSharedCheck_2747_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_val_2727_);
lean_dec(v___x_2723_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2747_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_decl_2731_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2743_; lean_object* v_fvarId_2746_; 
v_decl_2731_ = l_Lean_LocalDecl_setType(v_val_2727_, v_type_2719_);
v_fvarId_2746_ = lean_ctor_get(v_decl_2731_, 1);
lean_inc(v_fvarId_2746_);
v___y_2743_ = v_fvarId_2746_;
goto v___jp_2742_;
v___jp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v_decl_2731_);
v___x_2736_ = v___x_2729_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_decl_2731_);
v___x_2736_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_PersistentArray_set___redArg(v_decls_2721_, v___y_2734_, v___x_2736_);
lean_dec(v___y_2734_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2737_);
lean_ctor_set(v___x_2725_, 0, v___y_2733_);
v___x_2739_ = v___x_2725_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___y_2733_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_auxDeclToFullName_2722_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
v___jp_2742_:
{
lean_object* v___x_2744_; lean_object* v_index_2745_; 
lean_inc_ref(v_decl_2731_);
v___x_2744_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2720_, v___y_2743_, v_decl_2731_);
v_index_2745_ = lean_ctor_get(v_decl_2731_, 0);
lean_inc(v_index_2745_);
v___y_2733_ = v___x_2744_;
v___y_2734_ = v_index_2745_;
goto v___jp_2732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2752_){
_start:
{
lean_object* v_decls_2753_; lean_object* v_size_2754_; 
v_decls_2753_ = lean_ctor_get(v_lctx_2752_, 1);
lean_inc_ref(v_decls_2753_);
lean_dec_ref(v_lctx_2752_);
v_size_2754_ = lean_ctor_get(v_decls_2753_, 2);
lean_inc(v_size_2754_);
lean_dec_ref(v_decls_2753_);
return v_size_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2755_, lean_object* v_i_2756_){
_start:
{
lean_object* v_decls_2757_; lean_object* v_size_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_decls_2757_ = lean_ctor_get(v_lctx_2755_, 1);
v_size_2758_ = lean_ctor_get(v_decls_2757_, 2);
v___x_2759_ = lean_box(0);
v___x_2760_ = lean_nat_dec_lt(v_i_2756_, v_size_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_outOfBounds___redArg(v___x_2759_);
return v___x_2761_;
}
else
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2759_, v_decls_2757_, v_i_2756_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2763_, lean_object* v_i_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2763_, v_i_2764_);
lean_dec(v_i_2764_);
lean_dec_ref(v_lctx_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2766_, lean_object* v_f_2767_, lean_object* v_b_2768_, lean_object* v_decl_2769_){
_start:
{
if (lean_obj_tag(v_decl_2769_) == 0)
{
lean_object* v___x_2770_; 
lean_dec(v_f_2767_);
v___x_2770_ = lean_apply_2(v_toPure_2766_, lean_box(0), v_b_2768_);
return v___x_2770_;
}
else
{
lean_object* v_val_2771_; lean_object* v___x_2772_; 
lean_dec(v_toPure_2766_);
v_val_2771_ = lean_ctor_get(v_decl_2769_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v_decl_2769_, 1);
v___x_2772_ = lean_apply_2(v_f_2767_, v_b_2768_, v_val_2771_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2773_, lean_object* v_lctx_2774_, lean_object* v_f_2775_, lean_object* v_init_2776_, lean_object* v_start_2777_){
_start:
{
lean_object* v_toApplicative_2778_; lean_object* v_decls_2779_; lean_object* v_toPure_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
v_toApplicative_2778_ = lean_ctor_get(v_inst_2773_, 0);
v_decls_2779_ = lean_ctor_get(v_lctx_2774_, 1);
lean_inc_ref(v_decls_2779_);
lean_dec_ref(v_lctx_2774_);
v_toPure_2780_ = lean_ctor_get(v_toApplicative_2778_, 1);
lean_inc(v_toPure_2780_);
v___f_2781_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2781_, 0, v_toPure_2780_);
lean_closure_set(v___f_2781_, 1, v_f_2775_);
v___x_2782_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2773_, v_decls_2779_, v___f_2781_, v_init_2776_, v_start_2777_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2783_, lean_object* v_lctx_2784_, lean_object* v_f_2785_, lean_object* v_init_2786_, lean_object* v_start_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2783_, v_lctx_2784_, v_f_2785_, v_init_2786_, v_start_2787_);
lean_dec(v_start_2787_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_inst_2791_, lean_object* v_lctx_2792_, lean_object* v_f_2793_, lean_object* v_init_2794_, lean_object* v_start_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2791_, v_lctx_2792_, v_f_2793_, v_init_2794_, v_start_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2797_, lean_object* v_00_u03b2_2798_, lean_object* v_inst_2799_, lean_object* v_lctx_2800_, lean_object* v_f_2801_, lean_object* v_init_2802_, lean_object* v_start_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_LocalContext_foldlM(v_m_2797_, v_00_u03b2_2798_, v_inst_2799_, v_lctx_2800_, v_f_2801_, v_init_2802_, v_start_2803_);
lean_dec(v_start_2803_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2805_, lean_object* v_f_2806_, lean_object* v_decl_2807_, lean_object* v_b_2808_){
_start:
{
if (lean_obj_tag(v_decl_2807_) == 0)
{
lean_object* v___x_2809_; 
lean_dec(v_f_2806_);
v___x_2809_ = lean_apply_2(v_toPure_2805_, lean_box(0), v_b_2808_);
return v___x_2809_;
}
else
{
lean_object* v_val_2810_; lean_object* v___x_2811_; 
lean_dec(v_toPure_2805_);
v_val_2810_ = lean_ctor_get(v_decl_2807_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v_decl_2807_, 1);
v___x_2811_ = lean_apply_2(v_f_2806_, v_val_2810_, v_b_2808_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2812_, lean_object* v_lctx_2813_, lean_object* v_f_2814_, lean_object* v_init_2815_){
_start:
{
lean_object* v_toApplicative_2816_; lean_object* v_decls_2817_; lean_object* v_toPure_2818_; lean_object* v___f_2819_; lean_object* v___x_2820_; 
v_toApplicative_2816_ = lean_ctor_get(v_inst_2812_, 0);
v_decls_2817_ = lean_ctor_get(v_lctx_2813_, 1);
lean_inc_ref(v_decls_2817_);
lean_dec_ref(v_lctx_2813_);
v_toPure_2818_ = lean_ctor_get(v_toApplicative_2816_, 1);
lean_inc(v_toPure_2818_);
v___f_2819_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2819_, 0, v_toPure_2818_);
lean_closure_set(v___f_2819_, 1, v_f_2814_);
v___x_2820_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2812_, v_decls_2817_, v___f_2819_, v_init_2815_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2821_, lean_object* v_00_u03b2_2822_, lean_object* v_inst_2823_, lean_object* v_lctx_2824_, lean_object* v_f_2825_, lean_object* v_init_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2823_, v_lctx_2824_, v_f_2825_, v_init_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2828_, lean_object* v_f_2829_, lean_object* v_decl_2830_){
_start:
{
if (lean_obj_tag(v_decl_2830_) == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec(v_f_2829_);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_apply_2(v_toPure_2828_, lean_box(0), v___x_2831_);
return v___x_2832_;
}
else
{
lean_object* v_val_2833_; lean_object* v___x_2834_; 
lean_dec(v_toPure_2828_);
v_val_2833_ = lean_ctor_get(v_decl_2830_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_decl_2830_, 1);
v___x_2834_ = lean_apply_1(v_f_2829_, v_val_2833_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2835_, lean_object* v_lctx_2836_, lean_object* v_f_2837_, lean_object* v_start_2838_){
_start:
{
lean_object* v_toApplicative_2839_; lean_object* v_decls_2840_; lean_object* v_toPure_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; 
v_toApplicative_2839_ = lean_ctor_get(v_inst_2835_, 0);
v_decls_2840_ = lean_ctor_get(v_lctx_2836_, 1);
lean_inc_ref(v_decls_2840_);
lean_dec_ref(v_lctx_2836_);
v_toPure_2841_ = lean_ctor_get(v_toApplicative_2839_, 1);
lean_inc(v_toPure_2841_);
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2842_, 0, v_toPure_2841_);
lean_closure_set(v___f_2842_, 1, v_f_2837_);
v___x_2843_ = l_Lean_PersistentArray_forM___redArg(v_inst_2835_, v_decls_2840_, v___f_2842_, v_start_2838_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2844_, lean_object* v_lctx_2845_, lean_object* v_f_2846_, lean_object* v_start_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_LocalContext_forM___redArg(v_inst_2844_, v_lctx_2845_, v_f_2846_, v_start_2847_);
lean_dec(v_start_2847_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2849_, lean_object* v_inst_2850_, lean_object* v_lctx_2851_, lean_object* v_f_2852_, lean_object* v_start_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_LocalContext_forM___redArg(v_inst_2850_, v_lctx_2851_, v_f_2852_, v_start_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2855_, lean_object* v_inst_2856_, lean_object* v_lctx_2857_, lean_object* v_f_2858_, lean_object* v_start_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_LocalContext_forM(v_m_2855_, v_inst_2856_, v_lctx_2857_, v_f_2858_, v_start_2859_);
lean_dec(v_start_2859_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2861_, lean_object* v_f_2862_, lean_object* v_decl_2863_){
_start:
{
if (lean_obj_tag(v_decl_2863_) == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec(v_f_2862_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_apply_2(v_toPure_2861_, lean_box(0), v___x_2864_);
return v___x_2865_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2867_; 
lean_dec(v_toPure_2861_);
v_val_2866_ = lean_ctor_get(v_decl_2863_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v_decl_2863_, 1);
v___x_2867_ = lean_apply_1(v_f_2862_, v_val_2866_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2868_, lean_object* v_lctx_2869_, lean_object* v_f_2870_){
_start:
{
lean_object* v_toApplicative_2871_; lean_object* v_decls_2872_; lean_object* v_toPure_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; 
v_toApplicative_2871_ = lean_ctor_get(v_inst_2868_, 0);
v_decls_2872_ = lean_ctor_get(v_lctx_2869_, 1);
lean_inc_ref(v_decls_2872_);
lean_dec_ref(v_lctx_2869_);
v_toPure_2873_ = lean_ctor_get(v_toApplicative_2871_, 1);
lean_inc(v_toPure_2873_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2874_, 0, v_toPure_2873_);
lean_closure_set(v___f_2874_, 1, v_f_2870_);
v___x_2875_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2868_, v_decls_2872_, v___f_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2876_, lean_object* v_00_u03b2_2877_, lean_object* v_inst_2878_, lean_object* v_lctx_2879_, lean_object* v_f_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2878_, v_lctx_2879_, v_f_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2882_, lean_object* v_lctx_2883_, lean_object* v_f_2884_){
_start:
{
lean_object* v_toApplicative_2885_; lean_object* v_decls_2886_; lean_object* v_toPure_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; 
v_toApplicative_2885_ = lean_ctor_get(v_inst_2882_, 0);
v_decls_2886_ = lean_ctor_get(v_lctx_2883_, 1);
lean_inc_ref(v_decls_2886_);
lean_dec_ref(v_lctx_2883_);
v_toPure_2887_ = lean_ctor_get(v_toApplicative_2885_, 1);
lean_inc(v_toPure_2887_);
v___f_2888_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2888_, 0, v_toPure_2887_);
lean_closure_set(v___f_2888_, 1, v_f_2884_);
v___x_2889_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2882_, v_decls_2886_, v___f_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2890_, lean_object* v_00_u03b2_2891_, lean_object* v_inst_2892_, lean_object* v_lctx_2893_, lean_object* v_f_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2892_, v_lctx_2893_, v_f_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2896_, lean_object* v_f_2897_, lean_object* v_d_x3f_2898_, lean_object* v_b_2899_){
_start:
{
if (lean_obj_tag(v_d_x3f_2898_) == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v_f_2897_);
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_b_2899_);
v___x_2901_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_2900_);
return v___x_2901_;
}
else
{
lean_object* v_val_2902_; lean_object* v___x_2903_; 
lean_dec(v_toPure_2896_);
v_val_2902_ = lean_ctor_get(v_d_x3f_2898_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v_d_x3f_2898_, 1);
v___x_2903_ = lean_apply_2(v_f_2897_, v_val_2902_, v_b_2899_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2904_, lean_object* v_inst_2905_, lean_object* v_00_u03b2_2906_, lean_object* v_lctx_2907_, lean_object* v_init_2908_, lean_object* v_f_2909_){
_start:
{
lean_object* v_decls_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_decls_2910_ = lean_ctor_get(v_lctx_2907_, 1);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2911_, 0, v_toPure_2904_);
lean_closure_set(v___f_2911_, 1, v_f_2909_);
v___x_2912_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2905_, v_decls_2910_, v_init_2908_, v___f_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2913_, lean_object* v_inst_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_lctx_2916_, lean_object* v_init_2917_, lean_object* v_f_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2913_, v_inst_2914_, v_00_u03b2_2915_, v_lctx_2916_, v_init_2917_, v_f_2918_);
lean_dec_ref(v_lctx_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2920_){
_start:
{
lean_object* v_toApplicative_2921_; lean_object* v_toPure_2922_; lean_object* v___f_2923_; 
v_toApplicative_2921_ = lean_ctor_get(v_inst_2920_, 0);
v_toPure_2922_ = lean_ctor_get(v_toApplicative_2921_, 1);
lean_inc(v_toPure_2922_);
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2923_, 0, v_toPure_2922_);
lean_closure_set(v___f_2923_, 1, v_inst_2920_);
return v___f_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2924_, lean_object* v_inst_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2927_, lean_object* v_x1_2928_, lean_object* v_x2_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_apply_2(v_f_2927_, v_x1_2928_, v_x2_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2950_, lean_object* v_f_2951_, lean_object* v_init_2952_, lean_object* v_start_2953_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2954_, 0, v_f_2951_);
v___x_2955_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2956_ = l_Lean_LocalContext_foldlM___redArg(v___x_2955_, v_lctx_2950_, v___f_2954_, v_init_2952_, v_start_2953_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2957_, lean_object* v_f_2958_, lean_object* v_init_2959_, lean_object* v_start_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2957_, v_f_2958_, v_init_2959_, v_start_2960_);
lean_dec(v_start_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2962_, lean_object* v_lctx_2963_, lean_object* v_f_2964_, lean_object* v_init_2965_, lean_object* v_start_2966_){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2967_, 0, v_f_2964_);
v___x_2968_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2969_ = l_Lean_LocalContext_foldlM___redArg(v___x_2968_, v_lctx_2963_, v___f_2967_, v_init_2965_, v_start_2966_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_lctx_2971_, lean_object* v_f_2972_, lean_object* v_init_2973_, lean_object* v_start_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_LocalContext_foldl(v_00_u03b2_2970_, v_lctx_2971_, v_f_2972_, v_init_2973_, v_start_2974_);
lean_dec(v_start_2974_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2976_, lean_object* v_x1_2977_, lean_object* v_x2_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_apply_2(v_f_2976_, v_x1_2977_, v_x2_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2980_, lean_object* v_f_2981_, lean_object* v_init_2982_){
_start:
{
lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2983_, 0, v_f_2981_);
v___x_2984_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2985_ = l_Lean_LocalContext_foldrM___redArg(v___x_2984_, v_lctx_2980_, v___f_2983_, v_init_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2986_, lean_object* v_lctx_2987_, lean_object* v_f_2988_, lean_object* v_init_2989_){
_start:
{
lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2990_, 0, v_f_2988_);
v___x_2991_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2992_ = l_Lean_LocalContext_foldrM___redArg(v___x_2991_, v_lctx_2987_, v___f_2990_, v_init_2989_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_2993_, size_t v_i_2994_, size_t v_stop_2995_, lean_object* v_b_2996_){
_start:
{
lean_object* v___y_2998_; uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_eq(v_i_2994_, v_stop_2995_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_array_uget_borrowed(v_as_2993_, v_i_2994_);
if (lean_obj_tag(v___x_3003_) == 0)
{
v___y_2998_ = v_b_2996_;
goto v___jp_2997_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_b_2996_, v___x_3004_);
lean_dec(v_b_2996_);
v___y_2998_ = v___x_3005_;
goto v___jp_2997_;
}
}
else
{
return v_b_2996_;
}
v___jp_2997_:
{
size_t v___x_2999_; size_t v___x_3000_; 
v___x_2999_ = ((size_t)1ULL);
v___x_3000_ = lean_usize_add(v_i_2994_, v___x_2999_);
v_i_2994_ = v___x_3000_;
v_b_2996_ = v___y_2998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3006_, lean_object* v_i_3007_, lean_object* v_stop_3008_, lean_object* v_b_3009_){
_start:
{
size_t v_i_boxed_3010_; size_t v_stop_boxed_3011_; lean_object* v_res_3012_; 
v_i_boxed_3010_ = lean_unbox_usize(v_i_3007_);
lean_dec(v_i_3007_);
v_stop_boxed_3011_ = lean_unbox_usize(v_stop_3008_);
lean_dec(v_stop_3008_);
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3006_, v_i_boxed_3010_, v_stop_boxed_3011_, v_b_3009_);
lean_dec_ref(v_as_3006_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
if (lean_obj_tag(v_x_3013_) == 0)
{
lean_object* v_cs_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_cs_3015_ = lean_ctor_get(v_x_3013_, 0);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_cs_3015_);
v___x_3018_ = lean_nat_dec_lt(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
return v_x_3014_;
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3017_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3015_, v___x_3019_, v___x_3020_, v_x_3014_);
return v___x_3021_;
}
}
else
{
lean_object* v_vs_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_vs_3022_ = lean_ctor_get(v_x_3013_, 0);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_array_get_size(v_vs_3022_);
v___x_3025_ = lean_nat_dec_lt(v___x_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
return v_x_3014_;
}
else
{
size_t v___x_3026_; size_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = lean_usize_of_nat(v___x_3024_);
v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3022_, v___x_3026_, v___x_3027_, v_x_3014_);
return v___x_3028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3029_, size_t v_i_3030_, size_t v_stop_3031_, lean_object* v_b_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_usize_dec_eq(v_i_3030_, v_stop_3031_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; 
v___x_3034_ = lean_array_uget_borrowed(v_as_3029_, v_i_3030_);
v___x_3035_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3034_, v_b_3032_);
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_add(v_i_3030_, v___x_3036_);
v_i_3030_ = v___x_3037_;
v_b_3032_ = v___x_3035_;
goto _start;
}
else
{
return v_b_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3039_, lean_object* v_i_3040_, lean_object* v_stop_3041_, lean_object* v_b_3042_){
_start:
{
size_t v_i_boxed_3043_; size_t v_stop_boxed_3044_; lean_object* v_res_3045_; 
v_i_boxed_3043_ = lean_unbox_usize(v_i_3040_);
lean_dec(v_i_3040_);
v_stop_boxed_3044_ = lean_unbox_usize(v_stop_3041_);
lean_dec(v_stop_3041_);
v_res_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3039_, v_i_boxed_3043_, v_stop_boxed_3044_, v_b_3042_);
lean_dec_ref(v_as_3039_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3046_, v_x_3047_);
lean_dec_ref(v_x_3046_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3049_, size_t v_x_3050_, size_t v_x_3051_, lean_object* v_x_3052_){
_start:
{
if (lean_obj_tag(v_x_3049_) == 0)
{
lean_object* v_cs_3053_; lean_object* v___x_3054_; size_t v___x_3055_; lean_object* v_j_3056_; lean_object* v___x_3057_; size_t v___x_3058_; size_t v___x_3059_; size_t v___x_3060_; size_t v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_cs_3053_ = lean_ctor_get(v_x_3049_, 0);
v___x_3054_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3055_ = lean_usize_shift_right(v_x_3050_, v_x_3051_);
v_j_3056_ = lean_usize_to_nat(v___x_3055_);
v___x_3057_ = lean_array_get_borrowed(v___x_3054_, v_cs_3053_, v_j_3056_);
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_shift_left(v___x_3058_, v_x_3051_);
v___x_3060_ = lean_usize_sub(v___x_3059_, v___x_3058_);
v___x_3061_ = lean_usize_land(v_x_3050_, v___x_3060_);
v___x_3062_ = ((size_t)5ULL);
v___x_3063_ = lean_usize_sub(v_x_3051_, v___x_3062_);
v___x_3064_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3057_, v___x_3061_, v___x_3063_, v_x_3052_);
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = lean_nat_add(v_j_3056_, v___x_3065_);
lean_dec(v_j_3056_);
v___x_3067_ = lean_array_get_size(v_cs_3053_);
v___x_3068_ = lean_nat_dec_lt(v___x_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_dec(v___x_3066_);
return v___x_3064_;
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_usize_of_nat(v___x_3066_);
lean_dec(v___x_3066_);
v___x_3070_ = lean_usize_of_nat(v___x_3067_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3053_, v___x_3069_, v___x_3070_, v___x_3064_);
return v___x_3071_;
}
}
else
{
lean_object* v_vs_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_vs_3072_ = lean_ctor_get(v_x_3049_, 0);
v___x_3073_ = lean_usize_to_nat(v_x_3050_);
v___x_3074_ = lean_array_get_size(v_vs_3072_);
v___x_3075_ = lean_nat_dec_lt(v___x_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_dec(v___x_3073_);
return v_x_3052_;
}
else
{
size_t v___x_3076_; size_t v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_usize_of_nat(v___x_3073_);
lean_dec(v___x_3073_);
v___x_3077_ = lean_usize_of_nat(v___x_3074_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3072_, v___x_3076_, v___x_3077_, v_x_3052_);
return v___x_3078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_x_3082_){
_start:
{
size_t v_x_1185__boxed_3083_; size_t v_x_1186__boxed_3084_; lean_object* v_res_3085_; 
v_x_1185__boxed_3083_ = lean_unbox_usize(v_x_3080_);
lean_dec(v_x_3080_);
v_x_1186__boxed_3084_ = lean_unbox_usize(v_x_3081_);
lean_dec(v_x_3081_);
v_res_3085_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3079_, v_x_1185__boxed_3083_, v_x_1186__boxed_3084_, v_x_3082_);
lean_dec_ref(v_x_3079_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3086_, lean_object* v_init_3087_, lean_object* v_start_3088_){
_start:
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = lean_nat_dec_eq(v_start_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_object* v_root_3091_; lean_object* v_tail_3092_; size_t v_shift_3093_; lean_object* v_tailOff_3094_; uint8_t v___x_3095_; 
v_root_3091_ = lean_ctor_get(v_t_3086_, 0);
v_tail_3092_ = lean_ctor_get(v_t_3086_, 1);
v_shift_3093_ = lean_ctor_get_usize(v_t_3086_, 4);
v_tailOff_3094_ = lean_ctor_get(v_t_3086_, 3);
v___x_3095_ = lean_nat_dec_le(v_tailOff_3094_, v_start_3088_);
if (v___x_3095_ == 0)
{
size_t v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3096_ = lean_usize_of_nat(v_start_3088_);
v___x_3097_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3091_, v___x_3096_, v_shift_3093_, v_init_3087_);
v___x_3098_ = lean_array_get_size(v_tail_3092_);
v___x_3099_ = lean_nat_dec_lt(v___x_3089_, v___x_3098_);
if (v___x_3099_ == 0)
{
return v___x_3097_;
}
else
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = lean_usize_of_nat(v___x_3098_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3092_, v___x_3100_, v___x_3101_, v___x_3097_);
return v___x_3102_;
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = lean_nat_sub(v_start_3088_, v_tailOff_3094_);
v___x_3104_ = lean_array_get_size(v_tail_3092_);
v___x_3105_ = lean_nat_dec_lt(v___x_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec(v___x_3103_);
return v_init_3087_;
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_usize_of_nat(v___x_3103_);
lean_dec(v___x_3103_);
v___x_3107_ = lean_usize_of_nat(v___x_3104_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3092_, v___x_3106_, v___x_3107_, v_init_3087_);
return v___x_3108_;
}
}
}
else
{
lean_object* v_root_3109_; lean_object* v_tail_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v_root_3109_ = lean_ctor_get(v_t_3086_, 0);
v_tail_3110_ = lean_ctor_get(v_t_3086_, 1);
v___x_3111_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3109_, v_init_3087_);
v___x_3112_ = lean_array_get_size(v_tail_3110_);
v___x_3113_ = lean_nat_dec_lt(v___x_3089_, v___x_3112_);
if (v___x_3113_ == 0)
{
return v___x_3111_;
}
else
{
size_t v___x_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = ((size_t)0ULL);
v___x_3115_ = lean_usize_of_nat(v___x_3112_);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3110_, v___x_3114_, v___x_3115_, v___x_3111_);
return v___x_3116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3117_, lean_object* v_init_3118_, lean_object* v_start_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3117_, v_init_3118_, v_start_3119_);
lean_dec(v_start_3119_);
lean_dec_ref(v_t_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3121_, lean_object* v_init_3122_, lean_object* v_start_3123_){
_start:
{
lean_object* v_decls_3124_; lean_object* v___x_3125_; 
v_decls_3124_ = lean_ctor_get(v_lctx_3121_, 1);
v___x_3125_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3124_, v_init_3122_, v_start_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3126_, lean_object* v_init_3127_, lean_object* v_start_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3126_, v_init_3127_, v_start_3128_);
lean_dec(v_start_3128_);
lean_dec_ref(v_lctx_3126_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3130_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3130_, v___x_3131_, v___x_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_LocalContext_size(v_lctx_3133_);
lean_dec_ref(v_lctx_3133_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3135_, lean_object* v_x_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_apply_1(v_f_3135_, v_x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3138_, lean_object* v_f_3139_){
_start:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3140_, 0, v_f_3139_);
v___x_3141_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3142_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3141_, v_lctx_3138_, v___f_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3143_, lean_object* v_lctx_3144_, lean_object* v_f_3145_){
_start:
{
lean_object* v___f_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___f_3146_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3146_, 0, v_f_3145_);
v___x_3147_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3148_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3147_, v_lctx_3144_, v___f_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3149_, lean_object* v_f_3150_){
_start:
{
lean_object* v___f_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___f_3151_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3151_, 0, v_f_3150_);
v___x_3152_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3153_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3152_, v_lctx_3149_, v___f_3151_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3154_, lean_object* v_lctx_3155_, lean_object* v_f_3156_){
_start:
{
lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3157_, 0, v_f_3156_);
v___x_3158_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3159_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3158_, v_lctx_3155_, v___f_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3160_, lean_object* v_as_3161_, size_t v_i_3162_, size_t v_stop_3163_){
_start:
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_usize_dec_eq(v_i_3162_, v_stop_3163_);
if (v___x_3164_ == 0)
{
uint8_t v___x_3165_; uint8_t v___y_3167_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v_fvarId_3173_; uint8_t v___x_3174_; 
v___x_3165_ = 1;
v___x_3171_ = lean_array_uget_borrowed(v_as_3161_, v_i_3162_);
v___x_3172_ = l_Lean_Expr_fvarId_x21(v___x_3171_);
v_fvarId_3173_ = lean_ctor_get(v_val_3160_, 1);
v___x_3174_ = l_Lean_instBEqFVarId_beq(v___x_3172_, v_fvarId_3173_);
lean_dec(v___x_3172_);
v___y_3167_ = v___x_3174_;
goto v___jp_3166_;
v___jp_3166_:
{
if (v___y_3167_ == 0)
{
size_t v___x_3168_; size_t v___x_3169_; 
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_add(v_i_3162_, v___x_3168_);
v_i_3162_ = v___x_3169_;
goto _start;
}
else
{
return v___x_3165_;
}
}
}
else
{
uint8_t v___x_3175_; 
v___x_3175_ = 0;
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3176_, lean_object* v_as_3177_, lean_object* v_i_3178_, lean_object* v_stop_3179_){
_start:
{
size_t v_i_boxed_3180_; size_t v_stop_boxed_3181_; uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_i_boxed_3180_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_stop_boxed_3181_ = lean_unbox_usize(v_stop_3179_);
lean_dec(v_stop_3179_);
v_res_3182_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3176_, v_as_3177_, v_i_boxed_3180_, v_stop_boxed_3181_);
lean_dec_ref(v_as_3177_);
lean_dec_ref(v_val_3176_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3184_, lean_object* v_a_u2082_3185_, lean_object* v_exceptFVars_3186_, lean_object* v_i_3187_, lean_object* v_j_3188_){
_start:
{
lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_size_3204_; uint8_t v___x_3205_; 
v_size_3204_ = lean_ctor_get(v_a_u2081_3184_, 2);
v___x_3205_ = lean_nat_dec_lt(v_i_3187_, v_size_3204_);
if (v___x_3205_ == 0)
{
uint8_t v___x_3206_; 
lean_dec(v_j_3188_);
lean_dec(v_i_3187_);
v___x_3206_ = 1;
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3207_, v_a_u2081_3184_, v_i_3187_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_unsigned_to_nat(1u);
v___x_3210_ = lean_nat_add(v_i_3187_, v___x_3209_);
lean_dec(v_i_3187_);
v_i_3187_ = v___x_3210_;
goto _start;
}
else
{
lean_object* v_val_3212_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_val_3212_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3222_ = lean_unsigned_to_nat(0u);
v___x_3223_ = lean_array_get_size(v_exceptFVars_3186_);
v___x_3224_ = lean_nat_dec_lt(v___x_3222_, v___x_3223_);
if (v___x_3224_ == 0)
{
goto v___jp_3213_;
}
else
{
if (v___x_3224_ == 0)
{
goto v___jp_3213_;
}
else
{
size_t v___x_3225_; size_t v___x_3226_; uint8_t v___x_3227_; 
v___x_3225_ = ((size_t)0ULL);
v___x_3226_ = lean_usize_of_nat(v___x_3223_);
v___x_3227_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3212_, v_exceptFVars_3186_, v___x_3225_, v___x_3226_);
if (v___x_3227_ == 0)
{
goto v___jp_3213_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec(v_val_3212_);
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_add(v_i_3187_, v___x_3228_);
lean_dec(v_i_3187_);
v_i_3187_ = v___x_3229_;
goto _start;
}
}
}
v___jp_3213_:
{
lean_object* v_size_3214_; uint8_t v___x_3215_; 
v_size_3214_ = lean_ctor_get(v_a_u2082_3185_, 2);
v___x_3215_ = lean_nat_dec_lt(v_j_3188_, v_size_3214_);
if (v___x_3215_ == 0)
{
lean_dec(v_val_3212_);
lean_dec(v_j_3188_);
lean_dec(v_i_3187_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3207_, v_a_u2082_3185_, v_j_3188_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_dec(v_val_3212_);
v___x_3217_ = lean_unsigned_to_nat(1u);
v___x_3218_ = lean_nat_add(v_j_3188_, v___x_3217_);
lean_dec(v_j_3188_);
v_j_3188_ = v___x_3218_;
goto _start;
}
else
{
lean_object* v_val_3220_; lean_object* v_fvarId_3221_; 
v_val_3220_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___x_3216_, 1);
v_fvarId_3221_ = lean_ctor_get(v_val_3212_, 1);
lean_inc(v_fvarId_3221_);
lean_dec(v_val_3212_);
v___y_3201_ = v_val_3220_;
v___y_3202_ = v_fvarId_3221_;
goto v___jp_3200_;
}
}
}
}
}
v___jp_3189_:
{
uint8_t v___x_3192_; 
v___x_3192_ = l_Lean_instBEqFVarId_beq(v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec(v___y_3190_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_unsigned_to_nat(1u);
v___x_3194_ = lean_nat_add(v_j_3188_, v___x_3193_);
lean_dec(v_j_3188_);
v_j_3188_ = v___x_3194_;
goto _start;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = lean_unsigned_to_nat(1u);
v___x_3197_ = lean_nat_add(v_i_3187_, v___x_3196_);
lean_dec(v_i_3187_);
v___x_3198_ = lean_nat_add(v_j_3188_, v___x_3196_);
lean_dec(v_j_3188_);
v_i_3187_ = v___x_3197_;
v_j_3188_ = v___x_3198_;
goto _start;
}
}
v___jp_3200_:
{
lean_object* v_fvarId_3203_; 
v_fvarId_3203_ = lean_ctor_get(v___y_3201_, 1);
lean_inc(v_fvarId_3203_);
lean_dec_ref(v___y_3201_);
v___y_3190_ = v___y_3202_;
v___y_3191_ = v_fvarId_3203_;
goto v___jp_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3231_, lean_object* v_a_u2082_3232_, lean_object* v_exceptFVars_3233_, lean_object* v_i_3234_, lean_object* v_j_3235_){
_start:
{
uint8_t v_res_3236_; lean_object* v_r_3237_; 
v_res_3236_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3231_, v_a_u2082_3232_, v_exceptFVars_3233_, v_i_3234_, v_j_3235_);
lean_dec_ref(v_exceptFVars_3233_);
lean_dec_ref(v_a_u2082_3232_);
lean_dec_ref(v_a_u2081_3231_);
v_r_3237_ = lean_box(v_res_3236_);
return v_r_3237_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3238_, lean_object* v_lctx_u2082_3239_, lean_object* v_exceptFVars_3240_){
_start:
{
lean_object* v_decls_3241_; lean_object* v_decls_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_decls_3241_ = lean_ctor_get(v_lctx_u2081_3238_, 1);
v_decls_3242_ = lean_ctor_get(v_lctx_u2082_3239_, 1);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3241_, v_decls_3242_, v_exceptFVars_3240_, v___x_3243_, v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3245_, lean_object* v_lctx_u2082_3246_, lean_object* v_exceptFVars_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3245_, v_lctx_u2082_3246_, v_exceptFVars_3247_);
lean_dec_ref(v_exceptFVars_3247_);
lean_dec_ref(v_lctx_u2082_3246_);
lean_dec_ref(v_lctx_u2081_3245_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3251_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3252_ = lean_unsigned_to_nat(14u);
v___x_3253_ = lean_unsigned_to_nat(585u);
v___x_3254_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3255_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3256_ = l_mkPanicMessageWithDecl(v___x_3255_, v___x_3254_, v___x_3253_, v___x_3252_, v___x_3251_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3257_, lean_object* v_lctx_3258_, lean_object* v___x_3259_, uint8_t v_isLambda_3260_, uint8_t v_usedLetOnly_3261_, uint8_t v_generalizeNondepLet_3262_, lean_object* v_i_3263_, lean_object* v_x_3264_, lean_object* v_b_3265_){
_start:
{
lean_object* v_n_3267_; lean_object* v_ty_3268_; uint8_t v_bi_3269_; lean_object* v_x_3273_; lean_object* v___x_3274_; 
v_x_3273_ = lean_array_fget_borrowed(v_xs_3257_, v_i_3263_);
v___x_3274_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3258_, v_x_3273_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec_ref(v_b_3265_);
v___x_3275_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3276_ = l_panic___redArg(v___x_3259_, v___x_3275_);
return v___x_3276_;
}
else
{
lean_object* v_val_3277_; 
v_val_3277_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v___x_3274_, 1);
if (lean_obj_tag(v_val_3277_) == 0)
{
lean_object* v_userName_3278_; lean_object* v_type_3279_; uint8_t v_bi_3280_; 
v_userName_3278_ = lean_ctor_get(v_val_3277_, 2);
lean_inc(v_userName_3278_);
v_type_3279_ = lean_ctor_get(v_val_3277_, 3);
lean_inc_ref(v_type_3279_);
v_bi_3280_ = lean_ctor_get_uint8(v_val_3277_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3277_, 4);
v_n_3267_ = v_userName_3278_;
v_ty_3268_ = v_type_3279_;
v_bi_3269_ = v_bi_3280_;
goto v___jp_3266_;
}
else
{
lean_object* v_userName_3281_; lean_object* v_type_3282_; lean_object* v_value_3283_; uint8_t v_nondep_3284_; uint8_t v___y_3290_; 
v_userName_3281_ = lean_ctor_get(v_val_3277_, 2);
lean_inc(v_userName_3281_);
v_type_3282_ = lean_ctor_get(v_val_3277_, 3);
lean_inc_ref(v_type_3282_);
v_value_3283_ = lean_ctor_get(v_val_3277_, 4);
lean_inc_ref(v_value_3283_);
v_nondep_3284_ = lean_ctor_get_uint8(v_val_3277_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3277_, 5);
if (v_nondep_3284_ == 0)
{
v___y_3290_ = v_nondep_3284_;
goto v___jp_3289_;
}
else
{
if (v_generalizeNondepLet_3262_ == 0)
{
v___y_3290_ = v_generalizeNondepLet_3262_;
goto v___jp_3289_;
}
else
{
uint8_t v___x_3295_; 
lean_dec_ref(v_value_3283_);
v___x_3295_ = 0;
v_n_3267_ = v_userName_3281_;
v_ty_3268_ = v_type_3282_;
v_bi_3269_ = v___x_3295_;
goto v___jp_3266_;
}
}
v___jp_3285_:
{
lean_object* v_ty_3286_; lean_object* v_val_3287_; lean_object* v___x_3288_; 
v_ty_3286_ = lean_expr_abstract_range(v_type_3282_, v_i_3263_, v_xs_3257_);
lean_dec_ref(v_type_3282_);
v_val_3287_ = lean_expr_abstract_range(v_value_3283_, v_i_3263_, v_xs_3257_);
lean_dec_ref(v_value_3283_);
v___x_3288_ = l_Lean_Expr_letE___override(v_userName_3281_, v_ty_3286_, v_val_3287_, v_b_3265_, v_nondep_3284_);
return v___x_3288_;
}
v___jp_3289_:
{
if (v_usedLetOnly_3261_ == 0)
{
goto v___jp_3285_;
}
else
{
if (v___y_3290_ == 0)
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_expr_has_loose_bvar(v_b_3265_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec_ref(v_value_3283_);
lean_dec_ref(v_type_3282_);
lean_dec(v_userName_3281_);
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_expr_lower_loose_bvars(v_b_3265_, v___x_3293_, v___x_3293_);
lean_dec_ref(v_b_3265_);
return v___x_3294_;
}
else
{
goto v___jp_3285_;
}
}
else
{
goto v___jp_3285_;
}
}
}
}
}
v___jp_3266_:
{
lean_object* v_ty_3270_; 
v_ty_3270_ = lean_expr_abstract_range(v_ty_3268_, v_i_3263_, v_xs_3257_);
lean_dec_ref(v_ty_3268_);
if (v_isLambda_3260_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_mkForall(v_n_3267_, v_bi_3269_, v_ty_3270_, v_b_3265_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_mkLambda(v_n_3267_, v_bi_3269_, v_ty_3270_, v_b_3265_);
return v___x_3272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3296_, lean_object* v_lctx_3297_, lean_object* v___x_3298_, lean_object* v_isLambda_3299_, lean_object* v_usedLetOnly_3300_, lean_object* v_generalizeNondepLet_3301_, lean_object* v_i_3302_, lean_object* v_x_3303_, lean_object* v_b_3304_){
_start:
{
uint8_t v_isLambda_boxed_3305_; uint8_t v_usedLetOnly_boxed_3306_; uint8_t v_generalizeNondepLet_boxed_3307_; lean_object* v_res_3308_; 
v_isLambda_boxed_3305_ = lean_unbox(v_isLambda_3299_);
v_usedLetOnly_boxed_3306_ = lean_unbox(v_usedLetOnly_3300_);
v_generalizeNondepLet_boxed_3307_ = lean_unbox(v_generalizeNondepLet_3301_);
v_res_3308_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3296_, v_lctx_3297_, v___x_3298_, v_isLambda_boxed_3305_, v_usedLetOnly_boxed_3306_, v_generalizeNondepLet_boxed_3307_, v_i_3302_, v_x_3303_, v_b_3304_);
lean_dec(v_i_3302_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_xs_3296_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3309_, lean_object* v_lctx_3310_, lean_object* v_xs_3311_, lean_object* v_b_3312_, uint8_t v_usedLetOnly_3313_, uint8_t v_generalizeNondepLet_3314_){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___f_3319_; lean_object* v_b_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3315_ = l_Lean_instInhabitedExpr;
v___x_3316_ = lean_box(v_isLambda_3309_);
v___x_3317_ = lean_box(v_usedLetOnly_3313_);
v___x_3318_ = lean_box(v_generalizeNondepLet_3314_);
lean_inc_ref(v_xs_3311_);
v___f_3319_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3319_, 0, v_xs_3311_);
lean_closure_set(v___f_3319_, 1, v_lctx_3310_);
lean_closure_set(v___f_3319_, 2, v___x_3315_);
lean_closure_set(v___f_3319_, 3, v___x_3316_);
lean_closure_set(v___f_3319_, 4, v___x_3317_);
lean_closure_set(v___f_3319_, 5, v___x_3318_);
v_b_3320_ = lean_expr_abstract(v_b_3312_, v_xs_3311_);
v___x_3321_ = lean_array_get_size(v_xs_3311_);
lean_dec_ref(v_xs_3311_);
v___x_3322_ = l_Nat_foldRev___redArg(v___x_3321_, v___f_3319_, v_b_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3323_, lean_object* v_lctx_3324_, lean_object* v_xs_3325_, lean_object* v_b_3326_, lean_object* v_usedLetOnly_3327_, lean_object* v_generalizeNondepLet_3328_){
_start:
{
uint8_t v_isLambda_boxed_3329_; uint8_t v_usedLetOnly_boxed_3330_; uint8_t v_generalizeNondepLet_boxed_3331_; lean_object* v_res_3332_; 
v_isLambda_boxed_3329_ = lean_unbox(v_isLambda_3323_);
v_usedLetOnly_boxed_3330_ = lean_unbox(v_usedLetOnly_3327_);
v_generalizeNondepLet_boxed_3331_ = lean_unbox(v_generalizeNondepLet_3328_);
v_res_3332_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3329_, v_lctx_3324_, v_xs_3325_, v_b_3326_, v_usedLetOnly_boxed_3330_, v_generalizeNondepLet_boxed_3331_);
lean_dec_ref(v_b_3326_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3333_, lean_object* v_lctx_3334_, uint8_t v_usedLetOnly_3335_, uint8_t v_generalizeNondepLet_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v_zero_3339_; uint8_t v_isZero_3340_; 
v_zero_3339_ = lean_unsigned_to_nat(0u);
v_isZero_3340_ = lean_nat_dec_eq(v_x_3337_, v_zero_3339_);
if (v_isZero_3340_ == 1)
{
lean_dec(v_x_3337_);
lean_dec_ref(v_lctx_3334_);
return v_x_3338_;
}
else
{
lean_object* v_one_3341_; lean_object* v_n_3342_; lean_object* v_n_3344_; lean_object* v_ty_3345_; uint8_t v_bi_3346_; lean_object* v_x_3350_; lean_object* v___x_3351_; 
v_one_3341_ = lean_unsigned_to_nat(1u);
v_n_3342_ = lean_nat_sub(v_x_3337_, v_one_3341_);
lean_dec(v_x_3337_);
v_x_3350_ = lean_array_fget_borrowed(v_xs_3333_, v_n_3342_);
lean_inc_ref(v_lctx_3334_);
v___x_3351_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3334_, v_x_3350_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v_x_3338_);
v___x_3352_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3353_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3352_);
v_x_3337_ = v_n_3342_;
v_x_3338_ = v___x_3353_;
goto _start;
}
else
{
lean_object* v_val_3355_; 
v_val_3355_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v___x_3351_, 1);
if (lean_obj_tag(v_val_3355_) == 0)
{
lean_object* v_userName_3356_; lean_object* v_type_3357_; uint8_t v_bi_3358_; 
v_userName_3356_ = lean_ctor_get(v_val_3355_, 2);
lean_inc(v_userName_3356_);
v_type_3357_ = lean_ctor_get(v_val_3355_, 3);
lean_inc_ref(v_type_3357_);
v_bi_3358_ = lean_ctor_get_uint8(v_val_3355_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3355_, 4);
v_n_3344_ = v_userName_3356_;
v_ty_3345_ = v_type_3357_;
v_bi_3346_ = v_bi_3358_;
goto v___jp_3343_;
}
else
{
lean_object* v_userName_3359_; lean_object* v_type_3360_; lean_object* v_value_3361_; uint8_t v_nondep_3362_; uint8_t v___y_3369_; 
v_userName_3359_ = lean_ctor_get(v_val_3355_, 2);
lean_inc(v_userName_3359_);
v_type_3360_ = lean_ctor_get(v_val_3355_, 3);
lean_inc_ref(v_type_3360_);
v_value_3361_ = lean_ctor_get(v_val_3355_, 4);
lean_inc_ref(v_value_3361_);
v_nondep_3362_ = lean_ctor_get_uint8(v_val_3355_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3355_, 5);
if (v_nondep_3362_ == 0)
{
v___y_3369_ = v_nondep_3362_;
goto v___jp_3368_;
}
else
{
if (v_generalizeNondepLet_3336_ == 0)
{
v___y_3369_ = v_generalizeNondepLet_3336_;
goto v___jp_3368_;
}
else
{
uint8_t v___x_3373_; 
lean_dec_ref(v_value_3361_);
v___x_3373_ = 0;
v_n_3344_ = v_userName_3359_;
v_ty_3345_ = v_type_3360_;
v_bi_3346_ = v___x_3373_;
goto v___jp_3343_;
}
}
v___jp_3363_:
{
lean_object* v_ty_3364_; lean_object* v_val_3365_; lean_object* v___x_3366_; 
v_ty_3364_ = lean_expr_abstract_range(v_type_3360_, v_n_3342_, v_xs_3333_);
lean_dec_ref(v_type_3360_);
v_val_3365_ = lean_expr_abstract_range(v_value_3361_, v_n_3342_, v_xs_3333_);
lean_dec_ref(v_value_3361_);
v___x_3366_ = l_Lean_Expr_letE___override(v_userName_3359_, v_ty_3364_, v_val_3365_, v_x_3338_, v_nondep_3362_);
v_x_3337_ = v_n_3342_;
v_x_3338_ = v___x_3366_;
goto _start;
}
v___jp_3368_:
{
if (v_usedLetOnly_3335_ == 0)
{
goto v___jp_3363_;
}
else
{
if (v___y_3369_ == 0)
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_expr_has_loose_bvar(v_x_3338_, v_zero_3339_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_dec_ref(v_value_3361_);
lean_dec_ref(v_type_3360_);
lean_dec(v_userName_3359_);
v___x_3371_ = lean_expr_lower_loose_bvars(v_x_3338_, v_one_3341_, v_one_3341_);
lean_dec_ref(v_x_3338_);
v_x_3337_ = v_n_3342_;
v_x_3338_ = v___x_3371_;
goto _start;
}
else
{
goto v___jp_3363_;
}
}
else
{
goto v___jp_3363_;
}
}
}
}
}
v___jp_3343_:
{
lean_object* v_ty_3347_; lean_object* v___x_3348_; 
v_ty_3347_ = lean_expr_abstract_range(v_ty_3345_, v_n_3342_, v_xs_3333_);
lean_dec_ref(v_ty_3345_);
v___x_3348_ = l_Lean_mkLambda(v_n_3344_, v_bi_3346_, v_ty_3347_, v_x_3338_);
v_x_3337_ = v_n_3342_;
v_x_3338_ = v___x_3348_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3374_, lean_object* v_lctx_3375_, lean_object* v_usedLetOnly_3376_, lean_object* v_generalizeNondepLet_3377_, lean_object* v_x_3378_, lean_object* v_x_3379_){
_start:
{
uint8_t v_usedLetOnly_boxed_3380_; uint8_t v_generalizeNondepLet_boxed_3381_; lean_object* v_res_3382_; 
v_usedLetOnly_boxed_3380_ = lean_unbox(v_usedLetOnly_3376_);
v_generalizeNondepLet_boxed_3381_ = lean_unbox(v_generalizeNondepLet_3377_);
v_res_3382_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3374_, v_lctx_3375_, v_usedLetOnly_boxed_3380_, v_generalizeNondepLet_boxed_3381_, v_x_3378_, v_x_3379_);
lean_dec_ref(v_xs_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3383_, lean_object* v_lctx_3384_, uint8_t v_usedLetOnly_3385_, uint8_t v_generalizeNondepLet_3386_, lean_object* v_x_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v_zero_3389_; uint8_t v_isZero_3390_; 
v_zero_3389_ = lean_unsigned_to_nat(0u);
v_isZero_3390_ = lean_nat_dec_eq(v_x_3387_, v_zero_3389_);
if (v_isZero_3390_ == 1)
{
lean_dec_ref(v_lctx_3384_);
return v_x_3388_;
}
else
{
lean_object* v_one_3391_; lean_object* v_n_3392_; lean_object* v_n_3394_; lean_object* v_ty_3395_; uint8_t v_bi_3396_; lean_object* v_x_3400_; lean_object* v___x_3401_; 
v_one_3391_ = lean_unsigned_to_nat(1u);
v_n_3392_ = lean_nat_sub(v_x_3387_, v_one_3391_);
v_x_3400_ = lean_array_fget_borrowed(v_xs_3383_, v_n_3392_);
lean_inc_ref(v_lctx_3384_);
v___x_3401_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3384_, v_x_3400_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_x_3388_);
v___x_3402_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3403_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3402_);
v___x_3404_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3383_, v_lctx_3384_, v_usedLetOnly_3385_, v_generalizeNondepLet_3386_, v_n_3392_, v___x_3403_);
return v___x_3404_;
}
else
{
lean_object* v_val_3405_; 
v_val_3405_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3401_, 1);
if (lean_obj_tag(v_val_3405_) == 0)
{
lean_object* v_userName_3406_; lean_object* v_type_3407_; uint8_t v_bi_3408_; 
v_userName_3406_ = lean_ctor_get(v_val_3405_, 2);
lean_inc(v_userName_3406_);
v_type_3407_ = lean_ctor_get(v_val_3405_, 3);
lean_inc_ref(v_type_3407_);
v_bi_3408_ = lean_ctor_get_uint8(v_val_3405_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3405_, 4);
v_n_3394_ = v_userName_3406_;
v_ty_3395_ = v_type_3407_;
v_bi_3396_ = v_bi_3408_;
goto v___jp_3393_;
}
else
{
lean_object* v_userName_3409_; lean_object* v_type_3410_; lean_object* v_value_3411_; uint8_t v_nondep_3412_; uint8_t v___y_3419_; 
v_userName_3409_ = lean_ctor_get(v_val_3405_, 2);
lean_inc(v_userName_3409_);
v_type_3410_ = lean_ctor_get(v_val_3405_, 3);
lean_inc_ref(v_type_3410_);
v_value_3411_ = lean_ctor_get(v_val_3405_, 4);
lean_inc_ref(v_value_3411_);
v_nondep_3412_ = lean_ctor_get_uint8(v_val_3405_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3405_, 5);
if (v_nondep_3412_ == 0)
{
v___y_3419_ = v_nondep_3412_;
goto v___jp_3418_;
}
else
{
if (v_generalizeNondepLet_3386_ == 0)
{
v___y_3419_ = v_generalizeNondepLet_3386_;
goto v___jp_3418_;
}
else
{
uint8_t v___x_3423_; 
lean_dec_ref(v_value_3411_);
v___x_3423_ = 0;
v_n_3394_ = v_userName_3409_;
v_ty_3395_ = v_type_3410_;
v_bi_3396_ = v___x_3423_;
goto v___jp_3393_;
}
}
v___jp_3413_:
{
lean_object* v_ty_3414_; lean_object* v_val_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_ty_3414_ = lean_expr_abstract_range(v_type_3410_, v_n_3392_, v_xs_3383_);
lean_dec_ref(v_type_3410_);
v_val_3415_ = lean_expr_abstract_range(v_value_3411_, v_n_3392_, v_xs_3383_);
lean_dec_ref(v_value_3411_);
v___x_3416_ = l_Lean_Expr_letE___override(v_userName_3409_, v_ty_3414_, v_val_3415_, v_x_3388_, v_nondep_3412_);
v___x_3417_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3383_, v_lctx_3384_, v_usedLetOnly_3385_, v_generalizeNondepLet_3386_, v_n_3392_, v___x_3416_);
return v___x_3417_;
}
v___jp_3418_:
{
if (v_usedLetOnly_3385_ == 0)
{
goto v___jp_3413_;
}
else
{
if (v___y_3419_ == 0)
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_expr_has_loose_bvar(v_x_3388_, v_zero_3389_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v_value_3411_);
lean_dec_ref(v_type_3410_);
lean_dec(v_userName_3409_);
v___x_3421_ = lean_expr_lower_loose_bvars(v_x_3388_, v_one_3391_, v_one_3391_);
lean_dec_ref(v_x_3388_);
v___x_3422_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3383_, v_lctx_3384_, v_usedLetOnly_3385_, v_generalizeNondepLet_3386_, v_n_3392_, v___x_3421_);
return v___x_3422_;
}
else
{
goto v___jp_3413_;
}
}
else
{
goto v___jp_3413_;
}
}
}
}
}
v___jp_3393_:
{
lean_object* v_ty_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_ty_3397_ = lean_expr_abstract_range(v_ty_3395_, v_n_3392_, v_xs_3383_);
lean_dec_ref(v_ty_3395_);
v___x_3398_ = l_Lean_mkLambda(v_n_3394_, v_bi_3396_, v_ty_3397_, v_x_3388_);
v___x_3399_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3383_, v_lctx_3384_, v_usedLetOnly_3385_, v_generalizeNondepLet_3386_, v_n_3392_, v___x_3398_);
return v___x_3399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3424_, lean_object* v_lctx_3425_, lean_object* v_usedLetOnly_3426_, lean_object* v_generalizeNondepLet_3427_, lean_object* v_x_3428_, lean_object* v_x_3429_){
_start:
{
uint8_t v_usedLetOnly_boxed_3430_; uint8_t v_generalizeNondepLet_boxed_3431_; lean_object* v_res_3432_; 
v_usedLetOnly_boxed_3430_ = lean_unbox(v_usedLetOnly_3426_);
v_generalizeNondepLet_boxed_3431_ = lean_unbox(v_generalizeNondepLet_3427_);
v_res_3432_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3424_, v_lctx_3425_, v_usedLetOnly_boxed_3430_, v_generalizeNondepLet_boxed_3431_, v_x_3428_, v_x_3429_);
lean_dec(v_x_3428_);
lean_dec_ref(v_xs_3424_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3433_, lean_object* v_xs_3434_, lean_object* v_b_3435_, uint8_t v_usedLetOnly_3436_, uint8_t v_generalizeNondepLet_3437_){
_start:
{
lean_object* v_b_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_b_3438_ = lean_expr_abstract(v_b_3435_, v_xs_3434_);
v___x_3439_ = lean_array_get_size(v_xs_3434_);
v___x_3440_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3434_, v_lctx_3433_, v_usedLetOnly_3436_, v_generalizeNondepLet_3437_, v___x_3439_, v_b_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3441_, lean_object* v_xs_3442_, lean_object* v_b_3443_, lean_object* v_usedLetOnly_3444_, lean_object* v_generalizeNondepLet_3445_){
_start:
{
uint8_t v_usedLetOnly_boxed_3446_; uint8_t v_generalizeNondepLet_boxed_3447_; lean_object* v_res_3448_; 
v_usedLetOnly_boxed_3446_ = lean_unbox(v_usedLetOnly_3444_);
v_generalizeNondepLet_boxed_3447_ = lean_unbox(v_generalizeNondepLet_3445_);
v_res_3448_ = l_Lean_LocalContext_mkLambda(v_lctx_3441_, v_xs_3442_, v_b_3443_, v_usedLetOnly_boxed_3446_, v_generalizeNondepLet_boxed_3447_);
lean_dec_ref(v_b_3443_);
lean_dec_ref(v_xs_3442_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3449_, lean_object* v_lctx_3450_, uint8_t v_usedLetOnly_3451_, uint8_t v_generalizeNondepLet_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
lean_object* v_zero_3455_; uint8_t v_isZero_3456_; 
v_zero_3455_ = lean_unsigned_to_nat(0u);
v_isZero_3456_ = lean_nat_dec_eq(v_x_3453_, v_zero_3455_);
if (v_isZero_3456_ == 1)
{
lean_dec(v_x_3453_);
lean_dec_ref(v_lctx_3450_);
return v_x_3454_;
}
else
{
lean_object* v_one_3457_; lean_object* v_n_3458_; lean_object* v_n_3460_; lean_object* v_ty_3461_; uint8_t v_bi_3462_; lean_object* v_x_3466_; lean_object* v___x_3467_; 
v_one_3457_ = lean_unsigned_to_nat(1u);
v_n_3458_ = lean_nat_sub(v_x_3453_, v_one_3457_);
lean_dec(v_x_3453_);
v_x_3466_ = lean_array_fget_borrowed(v_xs_3449_, v_n_3458_);
lean_inc_ref(v_lctx_3450_);
v___x_3467_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3450_, v_x_3466_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec_ref(v_x_3454_);
v___x_3468_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3469_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3468_);
v_x_3453_ = v_n_3458_;
v_x_3454_ = v___x_3469_;
goto _start;
}
else
{
lean_object* v_val_3471_; 
v_val_3471_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v___x_3467_, 1);
if (lean_obj_tag(v_val_3471_) == 0)
{
lean_object* v_userName_3472_; lean_object* v_type_3473_; uint8_t v_bi_3474_; 
v_userName_3472_ = lean_ctor_get(v_val_3471_, 2);
lean_inc(v_userName_3472_);
v_type_3473_ = lean_ctor_get(v_val_3471_, 3);
lean_inc_ref(v_type_3473_);
v_bi_3474_ = lean_ctor_get_uint8(v_val_3471_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3471_, 4);
v_n_3460_ = v_userName_3472_;
v_ty_3461_ = v_type_3473_;
v_bi_3462_ = v_bi_3474_;
goto v___jp_3459_;
}
else
{
lean_object* v_userName_3475_; lean_object* v_type_3476_; lean_object* v_value_3477_; uint8_t v_nondep_3478_; uint8_t v___y_3485_; 
v_userName_3475_ = lean_ctor_get(v_val_3471_, 2);
lean_inc(v_userName_3475_);
v_type_3476_ = lean_ctor_get(v_val_3471_, 3);
lean_inc_ref(v_type_3476_);
v_value_3477_ = lean_ctor_get(v_val_3471_, 4);
lean_inc_ref(v_value_3477_);
v_nondep_3478_ = lean_ctor_get_uint8(v_val_3471_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3471_, 5);
if (v_nondep_3478_ == 0)
{
v___y_3485_ = v_nondep_3478_;
goto v___jp_3484_;
}
else
{
if (v_generalizeNondepLet_3452_ == 0)
{
v___y_3485_ = v_generalizeNondepLet_3452_;
goto v___jp_3484_;
}
else
{
uint8_t v___x_3489_; 
lean_dec_ref(v_value_3477_);
v___x_3489_ = 0;
v_n_3460_ = v_userName_3475_;
v_ty_3461_ = v_type_3476_;
v_bi_3462_ = v___x_3489_;
goto v___jp_3459_;
}
}
v___jp_3479_:
{
lean_object* v_ty_3480_; lean_object* v_val_3481_; lean_object* v___x_3482_; 
v_ty_3480_ = lean_expr_abstract_range(v_type_3476_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_type_3476_);
v_val_3481_ = lean_expr_abstract_range(v_value_3477_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_value_3477_);
v___x_3482_ = l_Lean_Expr_letE___override(v_userName_3475_, v_ty_3480_, v_val_3481_, v_x_3454_, v_nondep_3478_);
v_x_3453_ = v_n_3458_;
v_x_3454_ = v___x_3482_;
goto _start;
}
v___jp_3484_:
{
if (v_usedLetOnly_3451_ == 0)
{
goto v___jp_3479_;
}
else
{
if (v___y_3485_ == 0)
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_expr_has_loose_bvar(v_x_3454_, v_zero_3455_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref(v_value_3477_);
lean_dec_ref(v_type_3476_);
lean_dec(v_userName_3475_);
v___x_3487_ = lean_expr_lower_loose_bvars(v_x_3454_, v_one_3457_, v_one_3457_);
lean_dec_ref(v_x_3454_);
v_x_3453_ = v_n_3458_;
v_x_3454_ = v___x_3487_;
goto _start;
}
else
{
goto v___jp_3479_;
}
}
else
{
goto v___jp_3479_;
}
}
}
}
}
v___jp_3459_:
{
lean_object* v_ty_3463_; lean_object* v___x_3464_; 
v_ty_3463_ = lean_expr_abstract_range(v_ty_3461_, v_n_3458_, v_xs_3449_);
lean_dec_ref(v_ty_3461_);
v___x_3464_ = l_Lean_mkForall(v_n_3460_, v_bi_3462_, v_ty_3463_, v_x_3454_);
v_x_3453_ = v_n_3458_;
v_x_3454_ = v___x_3464_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3490_, lean_object* v_lctx_3491_, lean_object* v_usedLetOnly_3492_, lean_object* v_generalizeNondepLet_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
uint8_t v_usedLetOnly_boxed_3496_; uint8_t v_generalizeNondepLet_boxed_3497_; lean_object* v_res_3498_; 
v_usedLetOnly_boxed_3496_ = lean_unbox(v_usedLetOnly_3492_);
v_generalizeNondepLet_boxed_3497_ = lean_unbox(v_generalizeNondepLet_3493_);
v_res_3498_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3490_, v_lctx_3491_, v_usedLetOnly_boxed_3496_, v_generalizeNondepLet_boxed_3497_, v_x_3494_, v_x_3495_);
lean_dec_ref(v_xs_3490_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3499_, lean_object* v_lctx_3500_, uint8_t v_usedLetOnly_3501_, uint8_t v_generalizeNondepLet_3502_, lean_object* v_x_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v_zero_3505_; uint8_t v_isZero_3506_; 
v_zero_3505_ = lean_unsigned_to_nat(0u);
v_isZero_3506_ = lean_nat_dec_eq(v_x_3503_, v_zero_3505_);
if (v_isZero_3506_ == 1)
{
lean_dec_ref(v_lctx_3500_);
return v_x_3504_;
}
else
{
lean_object* v_one_3507_; lean_object* v_n_3508_; lean_object* v_n_3510_; lean_object* v_ty_3511_; uint8_t v_bi_3512_; lean_object* v_x_3516_; lean_object* v___x_3517_; 
v_one_3507_ = lean_unsigned_to_nat(1u);
v_n_3508_ = lean_nat_sub(v_x_3503_, v_one_3507_);
v_x_3516_ = lean_array_fget_borrowed(v_xs_3499_, v_n_3508_);
lean_inc_ref(v_lctx_3500_);
v___x_3517_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3500_, v_x_3516_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref(v_x_3504_);
v___x_3518_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3519_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3518_);
v___x_3520_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3499_, v_lctx_3500_, v_usedLetOnly_3501_, v_generalizeNondepLet_3502_, v_n_3508_, v___x_3519_);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; 
v_val_3521_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v___x_3517_, 1);
if (lean_obj_tag(v_val_3521_) == 0)
{
lean_object* v_userName_3522_; lean_object* v_type_3523_; uint8_t v_bi_3524_; 
v_userName_3522_ = lean_ctor_get(v_val_3521_, 2);
lean_inc(v_userName_3522_);
v_type_3523_ = lean_ctor_get(v_val_3521_, 3);
lean_inc_ref(v_type_3523_);
v_bi_3524_ = lean_ctor_get_uint8(v_val_3521_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3521_, 4);
v_n_3510_ = v_userName_3522_;
v_ty_3511_ = v_type_3523_;
v_bi_3512_ = v_bi_3524_;
goto v___jp_3509_;
}
else
{
lean_object* v_userName_3525_; lean_object* v_type_3526_; lean_object* v_value_3527_; uint8_t v_nondep_3528_; uint8_t v___y_3535_; 
v_userName_3525_ = lean_ctor_get(v_val_3521_, 2);
lean_inc(v_userName_3525_);
v_type_3526_ = lean_ctor_get(v_val_3521_, 3);
lean_inc_ref(v_type_3526_);
v_value_3527_ = lean_ctor_get(v_val_3521_, 4);
lean_inc_ref(v_value_3527_);
v_nondep_3528_ = lean_ctor_get_uint8(v_val_3521_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3521_, 5);
if (v_nondep_3528_ == 0)
{
v___y_3535_ = v_nondep_3528_;
goto v___jp_3534_;
}
else
{
if (v_generalizeNondepLet_3502_ == 0)
{
v___y_3535_ = v_generalizeNondepLet_3502_;
goto v___jp_3534_;
}
else
{
uint8_t v___x_3539_; 
lean_dec_ref(v_value_3527_);
v___x_3539_ = 0;
v_n_3510_ = v_userName_3525_;
v_ty_3511_ = v_type_3526_;
v_bi_3512_ = v___x_3539_;
goto v___jp_3509_;
}
}
v___jp_3529_:
{
lean_object* v_ty_3530_; lean_object* v_val_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_ty_3530_ = lean_expr_abstract_range(v_type_3526_, v_n_3508_, v_xs_3499_);
lean_dec_ref(v_type_3526_);
v_val_3531_ = lean_expr_abstract_range(v_value_3527_, v_n_3508_, v_xs_3499_);
lean_dec_ref(v_value_3527_);
v___x_3532_ = l_Lean_Expr_letE___override(v_userName_3525_, v_ty_3530_, v_val_3531_, v_x_3504_, v_nondep_3528_);
v___x_3533_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3499_, v_lctx_3500_, v_usedLetOnly_3501_, v_generalizeNondepLet_3502_, v_n_3508_, v___x_3532_);
return v___x_3533_;
}
v___jp_3534_:
{
if (v_usedLetOnly_3501_ == 0)
{
goto v___jp_3529_;
}
else
{
if (v___y_3535_ == 0)
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_expr_has_loose_bvar(v_x_3504_, v_zero_3505_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec_ref(v_value_3527_);
lean_dec_ref(v_type_3526_);
lean_dec(v_userName_3525_);
v___x_3537_ = lean_expr_lower_loose_bvars(v_x_3504_, v_one_3507_, v_one_3507_);
lean_dec_ref(v_x_3504_);
v___x_3538_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3499_, v_lctx_3500_, v_usedLetOnly_3501_, v_generalizeNondepLet_3502_, v_n_3508_, v___x_3537_);
return v___x_3538_;
}
else
{
goto v___jp_3529_;
}
}
else
{
goto v___jp_3529_;
}
}
}
}
}
v___jp_3509_:
{
lean_object* v_ty_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_ty_3513_ = lean_expr_abstract_range(v_ty_3511_, v_n_3508_, v_xs_3499_);
lean_dec_ref(v_ty_3511_);
v___x_3514_ = l_Lean_mkForall(v_n_3510_, v_bi_3512_, v_ty_3513_, v_x_3504_);
v___x_3515_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3499_, v_lctx_3500_, v_usedLetOnly_3501_, v_generalizeNondepLet_3502_, v_n_3508_, v___x_3514_);
return v___x_3515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3540_, lean_object* v_lctx_3541_, lean_object* v_usedLetOnly_3542_, lean_object* v_generalizeNondepLet_3543_, lean_object* v_x_3544_, lean_object* v_x_3545_){
_start:
{
uint8_t v_usedLetOnly_boxed_3546_; uint8_t v_generalizeNondepLet_boxed_3547_; lean_object* v_res_3548_; 
v_usedLetOnly_boxed_3546_ = lean_unbox(v_usedLetOnly_3542_);
v_generalizeNondepLet_boxed_3547_ = lean_unbox(v_generalizeNondepLet_3543_);
v_res_3548_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3540_, v_lctx_3541_, v_usedLetOnly_boxed_3546_, v_generalizeNondepLet_boxed_3547_, v_x_3544_, v_x_3545_);
lean_dec(v_x_3544_);
lean_dec_ref(v_xs_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3549_, lean_object* v_xs_3550_, lean_object* v_b_3551_, uint8_t v_usedLetOnly_3552_, uint8_t v_generalizeNondepLet_3553_){
_start:
{
lean_object* v_b_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_b_3554_ = lean_expr_abstract(v_b_3551_, v_xs_3550_);
v___x_3555_ = lean_array_get_size(v_xs_3550_);
v___x_3556_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3550_, v_lctx_3549_, v_usedLetOnly_3552_, v_generalizeNondepLet_3553_, v___x_3555_, v_b_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3557_, lean_object* v_xs_3558_, lean_object* v_b_3559_, lean_object* v_usedLetOnly_3560_, lean_object* v_generalizeNondepLet_3561_){
_start:
{
uint8_t v_usedLetOnly_boxed_3562_; uint8_t v_generalizeNondepLet_boxed_3563_; lean_object* v_res_3564_; 
v_usedLetOnly_boxed_3562_ = lean_unbox(v_usedLetOnly_3560_);
v_generalizeNondepLet_boxed_3563_ = lean_unbox(v_generalizeNondepLet_3561_);
v_res_3564_ = l_Lean_LocalContext_mkForall(v_lctx_3557_, v_xs_3558_, v_b_3559_, v_usedLetOnly_boxed_3562_, v_generalizeNondepLet_boxed_3563_);
lean_dec_ref(v_b_3559_);
lean_dec_ref(v_xs_3558_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3565_, lean_object* v_p_3566_, lean_object* v_d_3567_){
_start:
{
if (lean_obj_tag(v_d_3567_) == 0)
{
uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v_p_3566_);
v___x_3568_ = 0;
v___x_3569_ = lean_box(v___x_3568_);
v___x_3570_ = lean_apply_2(v_toPure_3565_, lean_box(0), v___x_3569_);
return v___x_3570_;
}
else
{
lean_object* v_val_3571_; lean_object* v___x_3572_; 
lean_dec(v_toPure_3565_);
v_val_3571_ = lean_ctor_get(v_d_3567_, 0);
lean_inc(v_val_3571_);
lean_dec_ref_known(v_d_3567_, 1);
v___x_3572_ = lean_apply_1(v_p_3566_, v_val_3571_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3573_, lean_object* v_lctx_3574_, lean_object* v_p_3575_){
_start:
{
lean_object* v_toApplicative_3576_; lean_object* v_decls_3577_; lean_object* v_toPure_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; 
v_toApplicative_3576_ = lean_ctor_get(v_inst_3573_, 0);
v_decls_3577_ = lean_ctor_get(v_lctx_3574_, 1);
lean_inc_ref(v_decls_3577_);
lean_dec_ref(v_lctx_3574_);
v_toPure_3578_ = lean_ctor_get(v_toApplicative_3576_, 1);
lean_inc(v_toPure_3578_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3579_, 0, v_toPure_3578_);
lean_closure_set(v___f_3579_, 1, v_p_3575_);
v___x_3580_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3573_, v_decls_3577_, v___f_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3581_, lean_object* v_inst_3582_, lean_object* v_lctx_3583_, lean_object* v_p_3584_){
_start:
{
lean_object* v_toApplicative_3585_; lean_object* v_decls_3586_; lean_object* v_toPure_3587_; lean_object* v___f_3588_; lean_object* v___x_3589_; 
v_toApplicative_3585_ = lean_ctor_get(v_inst_3582_, 0);
v_decls_3586_ = lean_ctor_get(v_lctx_3583_, 1);
lean_inc_ref(v_decls_3586_);
lean_dec_ref(v_lctx_3583_);
v_toPure_3587_ = lean_ctor_get(v_toApplicative_3585_, 1);
lean_inc(v_toPure_3587_);
v___f_3588_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3588_, 0, v_toPure_3587_);
lean_closure_set(v___f_3588_, 1, v_p_3584_);
v___x_3589_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3582_, v_decls_3586_, v___f_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3590_, uint8_t v_b_3591_){
_start:
{
if (v_b_3591_ == 0)
{
uint8_t v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = 1;
v___x_3593_ = lean_box(v___x_3592_);
v___x_3594_ = lean_apply_2(v_toPure_3590_, lean_box(0), v___x_3593_);
return v___x_3594_;
}
else
{
uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = 0;
v___x_3596_ = lean_box(v___x_3595_);
v___x_3597_ = lean_apply_2(v_toPure_3590_, lean_box(0), v___x_3596_);
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3598_, lean_object* v_b_3599_){
_start:
{
uint8_t v_b_boxed_3600_; lean_object* v_res_3601_; 
v_b_boxed_3600_ = lean_unbox(v_b_3599_);
v_res_3601_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3598_, v_b_boxed_3600_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3602_, lean_object* v_toBind_3603_, lean_object* v___f_3604_, lean_object* v_p_3605_, lean_object* v_v_3606_){
_start:
{
if (lean_obj_tag(v_v_3606_) == 0)
{
uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec(v_p_3605_);
v___x_3607_ = 1;
v___x_3608_ = lean_box(v___x_3607_);
v___x_3609_ = lean_apply_2(v_toPure_3602_, lean_box(0), v___x_3608_);
v___x_3610_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v___x_3609_, v___f_3604_);
return v___x_3610_;
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_dec(v_toPure_3602_);
v_val_3611_ = lean_ctor_get(v_v_3606_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_v_3606_, 1);
v___x_3612_ = lean_apply_1(v_p_3605_, v_val_3611_);
v___x_3613_ = lean_apply_4(v_toBind_3603_, lean_box(0), lean_box(0), v___x_3612_, v___f_3604_);
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3614_, lean_object* v_lctx_3615_, lean_object* v_p_3616_){
_start:
{
lean_object* v_toApplicative_3617_; lean_object* v_decls_3618_; lean_object* v_toBind_3619_; lean_object* v_toPure_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_toApplicative_3617_ = lean_ctor_get(v_inst_3614_, 0);
v_decls_3618_ = lean_ctor_get(v_lctx_3615_, 1);
lean_inc_ref(v_decls_3618_);
lean_dec_ref(v_lctx_3615_);
v_toBind_3619_ = lean_ctor_get(v_inst_3614_, 1);
lean_inc_n(v_toBind_3619_, 2);
v_toPure_3620_ = lean_ctor_get(v_toApplicative_3617_, 1);
lean_inc_n(v_toPure_3620_, 2);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3621_, 0, v_toPure_3620_);
lean_inc_ref(v___f_3621_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3622_, 0, v_toPure_3620_);
lean_closure_set(v___f_3622_, 1, v_toBind_3619_);
lean_closure_set(v___f_3622_, 2, v___f_3621_);
lean_closure_set(v___f_3622_, 3, v_p_3616_);
v___x_3623_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3614_, v_decls_3618_, v___f_3622_);
v___x_3624_ = lean_apply_4(v_toBind_3619_, lean_box(0), lean_box(0), v___x_3623_, v___f_3621_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3625_, lean_object* v_inst_3626_, lean_object* v_lctx_3627_, lean_object* v_p_3628_){
_start:
{
lean_object* v_toApplicative_3629_; lean_object* v_decls_3630_; lean_object* v_toBind_3631_; lean_object* v_toPure_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v_toApplicative_3629_ = lean_ctor_get(v_inst_3626_, 0);
v_decls_3630_ = lean_ctor_get(v_lctx_3627_, 1);
lean_inc_ref(v_decls_3630_);
lean_dec_ref(v_lctx_3627_);
v_toBind_3631_ = lean_ctor_get(v_inst_3626_, 1);
lean_inc_n(v_toBind_3631_, 2);
v_toPure_3632_ = lean_ctor_get(v_toApplicative_3629_, 1);
lean_inc_n(v_toPure_3632_, 2);
v___f_3633_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3633_, 0, v_toPure_3632_);
lean_inc_ref(v___f_3633_);
v___f_3634_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3634_, 0, v_toPure_3632_);
lean_closure_set(v___f_3634_, 1, v_toBind_3631_);
lean_closure_set(v___f_3634_, 2, v___f_3633_);
lean_closure_set(v___f_3634_, 3, v_p_3628_);
v___x_3635_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3626_, v_decls_3630_, v___f_3634_);
v___x_3636_ = lean_apply_4(v_toBind_3631_, lean_box(0), lean_box(0), v___x_3635_, v___f_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3637_, lean_object* v_d_3638_){
_start:
{
if (lean_obj_tag(v_d_3638_) == 0)
{
uint8_t v___x_3639_; 
lean_dec_ref(v_p_3637_);
v___x_3639_ = 0;
return v___x_3639_;
}
else
{
lean_object* v_val_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_val_3640_ = lean_ctor_get(v_d_3638_, 0);
lean_inc(v_val_3640_);
lean_dec_ref_known(v_d_3638_, 1);
v___x_3641_ = lean_apply_1(v_p_3637_, v_val_3640_);
v___x_3642_ = lean_unbox(v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3643_, lean_object* v_d_3644_){
_start:
{
uint8_t v_res_3645_; lean_object* v_r_3646_; 
v_res_3645_ = l_Lean_LocalContext_any___lam__0(v_p_3643_, v_d_3644_);
v_r_3646_ = lean_box(v_res_3645_);
return v_r_3646_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3647_, lean_object* v_p_3648_){
_start:
{
lean_object* v___x_3649_; lean_object* v_decls_3650_; lean_object* v___f_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3649_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3650_ = lean_ctor_get(v_lctx_3647_, 1);
lean_inc_ref(v_decls_3650_);
lean_dec_ref(v_lctx_3647_);
v___f_3651_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3651_, 0, v_p_3648_);
v___x_3652_ = l_Lean_PersistentArray_anyM___redArg(v___x_3649_, v_decls_3650_, v___f_3651_);
v___x_3653_ = lean_unbox(v___x_3652_);
lean_dec(v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3654_, lean_object* v_p_3655_){
_start:
{
uint8_t v_res_3656_; lean_object* v_r_3657_; 
v_res_3656_ = l_Lean_LocalContext_any(v_lctx_3654_, v_p_3655_);
v_r_3657_ = lean_box(v_res_3656_);
return v_r_3657_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3658_, lean_object* v_v_3659_){
_start:
{
if (lean_obj_tag(v_v_3659_) == 0)
{
uint8_t v___x_3660_; 
lean_dec_ref(v_p_3658_);
v___x_3660_ = 0;
return v___x_3660_;
}
else
{
lean_object* v_val_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v_val_3661_ = lean_ctor_get(v_v_3659_, 0);
lean_inc(v_val_3661_);
lean_dec_ref_known(v_v_3659_, 1);
v___x_3662_ = lean_apply_1(v_p_3658_, v_val_3661_);
v___x_3663_ = lean_unbox(v___x_3662_);
if (v___x_3663_ == 0)
{
uint8_t v___x_3664_; 
v___x_3664_ = 1;
return v___x_3664_;
}
else
{
uint8_t v___x_3665_; 
v___x_3665_ = 0;
return v___x_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3666_, lean_object* v_v_3667_){
_start:
{
uint8_t v_res_3668_; lean_object* v_r_3669_; 
v_res_3668_ = l_Lean_LocalContext_all___lam__0(v_p_3666_, v_v_3667_);
v_r_3669_ = lean_box(v_res_3668_);
return v_r_3669_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3670_, lean_object* v_p_3671_){
_start:
{
lean_object* v___x_3672_; lean_object* v_decls_3673_; lean_object* v___f_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3672_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3673_ = lean_ctor_get(v_lctx_3670_, 1);
lean_inc_ref(v_decls_3673_);
lean_dec_ref(v_lctx_3670_);
v___f_3674_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3674_, 0, v_p_3671_);
v___x_3675_ = l_Lean_PersistentArray_anyM___redArg(v___x_3672_, v_decls_3673_, v___f_3674_);
v___x_3676_ = lean_unbox(v___x_3675_);
lean_dec(v___x_3675_);
if (v___x_3676_ == 0)
{
uint8_t v___x_3677_; 
v___x_3677_ = 1;
return v___x_3677_;
}
else
{
uint8_t v___x_3678_; 
v___x_3678_ = 0;
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3679_, lean_object* v_p_3680_){
_start:
{
uint8_t v_res_3681_; lean_object* v_r_3682_; 
v_res_3681_ = l_Lean_LocalContext_all(v_lctx_3679_, v_p_3680_);
v_r_3682_ = lean_box(v_res_3681_);
return v_r_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3683_, lean_object* v_a_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_zero_3687_; uint8_t v_isZero_3688_; 
v_zero_3687_ = lean_unsigned_to_nat(0u);
v_isZero_3688_ = lean_nat_dec_eq(v_i_3683_, v_zero_3687_);
if (v_isZero_3688_ == 1)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec(v_i_3683_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_a_3684_);
lean_ctor_set(v___x_3689_, 1, v___y_3685_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v___y_3686_);
return v___x_3690_;
}
else
{
lean_object* v_decls_3691_; lean_object* v_size_3692_; lean_object* v___x_3693_; lean_object* v_one_3694_; lean_object* v_n_3695_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3712_; lean_object* v___y_3713_; uint8_t v___y_3714_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3724_; uint8_t v___x_3728_; 
v_decls_3691_ = lean_ctor_get(v_a_3684_, 1);
v_size_3692_ = lean_ctor_get(v_decls_3691_, 2);
v___x_3693_ = lean_box(0);
v_one_3694_ = lean_unsigned_to_nat(1u);
v_n_3695_ = lean_nat_sub(v_i_3683_, v_one_3694_);
lean_dec(v_i_3683_);
v___x_3728_ = lean_nat_dec_lt(v_n_3695_, v_size_3692_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = l_outOfBounds___redArg(v___x_3693_);
v___y_3724_ = v___x_3729_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3693_, v_decls_3691_, v_n_3695_);
v___y_3724_ = v___x_3730_;
goto v___jp_3723_;
}
v___jp_3696_:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_LocalContext_setUserName(v_a_3684_, v___y_3700_, v___y_3698_);
v_i_3683_ = v_n_3695_;
v_a_3684_ = v___x_3701_;
v___y_3685_ = v___y_3699_;
v___y_3686_ = v___y_3697_;
goto _start;
}
v___jp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_fst_3708_; lean_object* v_snd_3709_; lean_object* v_fvarId_3710_; 
lean_inc(v___y_3704_);
v___x_3706_ = l_Lean_NameSet_insert(v___y_3685_, v___y_3704_);
v___x_3707_ = l_Lean_sanitizeName(v___y_3704_, v___y_3686_);
v_fst_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_fst_3708_);
v_snd_3709_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_snd_3709_);
lean_dec_ref(v___x_3707_);
v_fvarId_3710_ = lean_ctor_get(v___y_3705_, 1);
lean_inc(v_fvarId_3710_);
lean_dec_ref(v___y_3705_);
v___y_3697_ = v_snd_3709_;
v___y_3698_ = v_fst_3708_;
v___y_3699_ = v___x_3706_;
v___y_3700_ = v_fvarId_3710_;
goto v___jp_3696_;
}
v___jp_3711_:
{
if (v___y_3714_ == 0)
{
lean_object* v___x_3715_; 
lean_dec_ref(v___y_3713_);
v___x_3715_ = l_Lean_NameSet_insert(v___y_3685_, v___y_3712_);
v_i_3683_ = v_n_3695_;
v___y_3685_ = v___x_3715_;
goto _start;
}
else
{
v___y_3704_ = v___y_3712_;
v___y_3705_ = v___y_3713_;
goto v___jp_3703_;
}
}
v___jp_3717_:
{
uint8_t v___x_3720_; 
v___x_3720_ = l_Lean_Name_hasMacroScopes(v___y_3719_);
if (v___x_3720_ == 0)
{
lean_object* v_userName_3721_; uint8_t v___x_3722_; 
v_userName_3721_ = lean_ctor_get(v___y_3718_, 2);
v___x_3722_ = l_Lean_NameSet_contains(v___y_3685_, v_userName_3721_);
v___y_3712_ = v___y_3719_;
v___y_3713_ = v___y_3718_;
v___y_3714_ = v___x_3722_;
goto v___jp_3711_;
}
else
{
v___y_3704_ = v___y_3719_;
v___y_3705_ = v___y_3718_;
goto v___jp_3703_;
}
}
v___jp_3723_:
{
if (lean_obj_tag(v___y_3724_) == 0)
{
v_i_3683_ = v_n_3695_;
goto _start;
}
else
{
lean_object* v_val_3726_; lean_object* v_userName_3727_; 
v_val_3726_ = lean_ctor_get(v___y_3724_, 0);
lean_inc(v_val_3726_);
lean_dec_ref_known(v___y_3724_, 1);
v_userName_3727_ = lean_ctor_get(v_val_3726_, 2);
lean_inc(v_userName_3727_);
v___y_3718_ = v_val_3726_;
v___y_3719_ = v_userName_3727_;
goto v___jp_3717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_options_3733_; uint8_t v___x_3734_; 
v_options_3733_ = lean_ctor_get(v_a_3732_, 0);
v___x_3734_ = l_Lean_getSanitizeNames(v_options_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_lctx_3731_);
lean_ctor_set(v___x_3735_, 1, v_a_3732_);
return v___x_3735_;
}
else
{
lean_object* v_decls_3736_; lean_object* v_size_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_fst_3740_; lean_object* v_snd_3741_; lean_object* v_fst_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_decls_3736_ = lean_ctor_get(v_lctx_3731_, 1);
v_size_3737_ = lean_ctor_get(v_decls_3736_, 2);
lean_inc(v_size_3737_);
v___x_3738_ = l_Lean_NameSet_empty;
v___x_3739_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3737_, v_lctx_3731_, v___x_3738_, v_a_3732_);
v_fst_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_fst_3740_);
v_snd_3741_ = lean_ctor_get(v___x_3739_, 1);
lean_inc(v_snd_3741_);
lean_dec_ref(v___x_3739_);
v_fst_3742_ = lean_ctor_get(v_fst_3740_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_fst_3740_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v_fst_3740_, 1);
lean_dec(v_unused_3750_);
v___x_3744_ = v_fst_3740_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_fst_3742_);
lean_dec(v_fst_3740_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 1, v_snd_3741_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_fst_3742_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_snd_3741_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3751_, lean_object* v_i_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3752_, v_a_3754_, v___y_3755_, v___y_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3758_, lean_object* v_i_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3758_, v_i_3759_, v_a_3760_, v_a_3761_, v___y_3762_, v___y_3763_);
lean_dec(v_n_3758_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3765_, lean_object* v_fvarId_3766_){
_start:
{
lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___x_3779_; 
lean_inc_ref(v_lctx_3765_);
v___x_3779_ = lean_local_ctx_find(v_lctx_3765_, v_fvarId_3766_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; 
lean_dec_ref(v_lctx_3765_);
v___x_3780_ = lean_box(0);
return v___x_3780_;
}
else
{
lean_object* v_val_3781_; lean_object* v___y_3783_; lean_object* v_userName_3788_; 
v_val_3781_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_val_3781_);
lean_dec_ref_known(v___x_3779_, 1);
v_userName_3788_ = lean_ctor_get(v_val_3781_, 2);
lean_inc(v_userName_3788_);
v___y_3783_ = v_userName_3788_;
goto v___jp_3782_;
v___jp_3782_:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3765_, v___y_3783_);
lean_dec_ref(v_lctx_3765_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; 
lean_dec(v___y_3783_);
lean_dec(v_val_3781_);
v___x_3785_ = lean_box(0);
return v___x_3785_;
}
else
{
lean_object* v_val_3786_; lean_object* v_fvarId_3787_; 
v_val_3786_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v___x_3784_, 1);
v_fvarId_3787_ = lean_ctor_get(v_val_3781_, 1);
lean_inc(v_fvarId_3787_);
lean_dec(v_val_3781_);
v___y_3775_ = v___y_3783_;
v___y_3776_ = v_val_3786_;
v___y_3777_ = v_fvarId_3787_;
goto v___jp_3774_;
}
}
}
v___jp_3767_:
{
uint8_t v___x_3771_; 
v___x_3771_ = l_Lean_instBEqFVarId_beq(v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec(v___y_3769_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
lean_dec(v___y_3768_);
v___x_3772_ = lean_box(0);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___y_3768_);
return v___x_3773_;
}
}
v___jp_3774_:
{
lean_object* v_fvarId_3778_; 
v_fvarId_3778_ = lean_ctor_get(v___y_3776_, 1);
lean_inc(v_fvarId_3778_);
lean_dec_ref(v___y_3776_);
v___y_3768_ = v___y_3775_;
v___y_3769_ = v___y_3777_;
v___y_3770_ = v_fvarId_3778_;
goto v___jp_3767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3789_, size_t v_i_3790_, lean_object* v_bs_3791_){
_start:
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_lt(v_i_3790_, v_sz_3789_);
if (v___x_3792_ == 0)
{
return v_bs_3791_;
}
else
{
lean_object* v_v_3793_; lean_object* v_snd_3794_; lean_object* v___x_3795_; lean_object* v_bs_x27_3796_; size_t v___x_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v_v_3793_ = lean_array_uget_borrowed(v_bs_3791_, v_i_3790_);
v_snd_3794_ = lean_ctor_get(v_v_3793_, 1);
lean_inc(v_snd_3794_);
v___x_3795_ = lean_unsigned_to_nat(0u);
v_bs_x27_3796_ = lean_array_uset(v_bs_3791_, v_i_3790_, v___x_3795_);
v___x_3797_ = ((size_t)1ULL);
v___x_3798_ = lean_usize_add(v_i_3790_, v___x_3797_);
v___x_3799_ = lean_array_uset(v_bs_x27_3796_, v_i_3790_, v_snd_3794_);
v_i_3790_ = v___x_3798_;
v_bs_3791_ = v___x_3799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_bs_3803_){
_start:
{
size_t v_sz_boxed_3804_; size_t v_i_boxed_3805_; lean_object* v_res_3806_; 
v_sz_boxed_3804_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3805_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3804_, v_i_boxed_3805_, v_bs_3803_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3807_, size_t v_sz_3808_, size_t v_i_3809_, lean_object* v_bs_3810_){
_start:
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_usize_dec_lt(v_i_3809_, v_sz_3808_);
if (v___x_3811_ == 0)
{
return v_bs_3810_;
}
else
{
lean_object* v_fvarIdToDecl_3812_; lean_object* v_v_3813_; lean_object* v___x_3814_; lean_object* v_bs_x27_3815_; lean_object* v___y_3817_; lean_object* v___x_3822_; 
v_fvarIdToDecl_3812_ = lean_ctor_get(v_lctx_3807_, 0);
v_v_3813_ = lean_array_uget(v_bs_3810_, v_i_3809_);
v___x_3814_ = lean_unsigned_to_nat(0u);
v_bs_x27_3815_ = lean_array_uset(v_bs_3810_, v_i_3809_, v___x_3814_);
v___x_3822_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3812_, v_v_3813_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3814_);
lean_ctor_set(v___x_3823_, 1, v_v_3813_);
v___y_3817_ = v___x_3823_;
goto v___jp_3816_;
}
else
{
lean_object* v_val_3824_; lean_object* v_index_3825_; lean_object* v___x_3826_; 
v_val_3824_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v___x_3822_, 1);
v_index_3825_ = lean_ctor_get(v_val_3824_, 0);
lean_inc(v_index_3825_);
lean_dec(v_val_3824_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_index_3825_);
lean_ctor_set(v___x_3826_, 1, v_v_3813_);
v___y_3817_ = v___x_3826_;
goto v___jp_3816_;
}
v___jp_3816_:
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_add(v_i_3809_, v___x_3818_);
v___x_3820_ = lean_array_uset(v_bs_x27_3815_, v_i_3809_, v___y_3817_);
v_i_3809_ = v___x_3819_;
v_bs_3810_ = v___x_3820_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3827_, lean_object* v_sz_3828_, lean_object* v_i_3829_, lean_object* v_bs_3830_){
_start:
{
size_t v_sz_boxed_3831_; size_t v_i_boxed_3832_; lean_object* v_res_3833_; 
v_sz_boxed_3831_ = lean_unbox_usize(v_sz_3828_);
lean_dec(v_sz_3828_);
v_i_boxed_3832_ = lean_unbox_usize(v_i_3829_);
lean_dec(v_i_3829_);
v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3827_, v_sz_boxed_3831_, v_i_boxed_3832_, v_bs_3830_);
lean_dec_ref(v_lctx_3827_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3834_, lean_object* v_pivot_3835_, lean_object* v_as_3836_, lean_object* v_i_3837_, lean_object* v_k_3838_){
_start:
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_nat_dec_lt(v_k_3838_, v_hi_3834_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_k_3838_);
v___x_3840_ = lean_array_fswap(v_as_3836_, v_i_3837_, v_hi_3834_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_i_3837_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
return v___x_3841_;
}
else
{
lean_object* v___x_3842_; lean_object* v_fst_3843_; lean_object* v_fst_3844_; uint8_t v___x_3845_; 
v___x_3842_ = lean_array_fget_borrowed(v_as_3836_, v_k_3838_);
v_fst_3843_ = lean_ctor_get(v___x_3842_, 0);
v_fst_3844_ = lean_ctor_get(v_pivot_3835_, 0);
v___x_3845_ = lean_nat_dec_lt(v_fst_3843_, v_fst_3844_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_nat_add(v_k_3838_, v___x_3846_);
lean_dec(v_k_3838_);
v_k_3838_ = v___x_3847_;
goto _start;
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3849_ = lean_array_fswap(v_as_3836_, v_i_3837_, v_k_3838_);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_add(v_i_3837_, v___x_3850_);
lean_dec(v_i_3837_);
v___x_3852_ = lean_nat_add(v_k_3838_, v___x_3850_);
lean_dec(v_k_3838_);
v_as_3836_ = v___x_3849_;
v_i_3837_ = v___x_3851_;
v_k_3838_ = v___x_3852_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3854_, lean_object* v_pivot_3855_, lean_object* v_as_3856_, lean_object* v_i_3857_, lean_object* v_k_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3854_, v_pivot_3855_, v_as_3856_, v_i_3857_, v_k_3858_);
lean_dec_ref(v_pivot_3855_);
lean_dec(v_hi_3854_);
return v_res_3859_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3860_, lean_object* v_i_3861_){
_start:
{
lean_object* v_fst_3862_; lean_object* v_fst_3863_; uint8_t v___x_3864_; 
v_fst_3862_ = lean_ctor_get(v_h_3860_, 0);
v_fst_3863_ = lean_ctor_get(v_i_3861_, 0);
v___x_3864_ = lean_nat_dec_lt(v_fst_3862_, v_fst_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3865_, lean_object* v_i_3866_){
_start:
{
uint8_t v_res_3867_; lean_object* v_r_3868_; 
v_res_3867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3865_, v_i_3866_);
lean_dec_ref(v_i_3866_);
lean_dec_ref(v_h_3865_);
v_r_3868_ = lean_box(v_res_3867_);
return v_r_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3869_, lean_object* v_as_3870_, lean_object* v_lo_3871_, lean_object* v_hi_3872_){
_start:
{
lean_object* v___y_3874_; uint8_t v___x_3884_; 
v___x_3884_ = lean_nat_dec_lt(v_lo_3871_, v_hi_3872_);
if (v___x_3884_ == 0)
{
lean_dec(v_lo_3871_);
return v_as_3870_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_mid_3887_; lean_object* v___y_3889_; lean_object* v___y_3895_; lean_object* v___x_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3885_ = lean_nat_add(v_lo_3871_, v_hi_3872_);
v___x_3886_ = lean_unsigned_to_nat(1u);
v_mid_3887_ = lean_nat_shiftr(v___x_3885_, v___x_3886_);
lean_dec(v___x_3885_);
v___x_3900_ = lean_array_fget_borrowed(v_as_3870_, v_mid_3887_);
v___x_3901_ = lean_array_fget_borrowed(v_as_3870_, v_lo_3871_);
v___x_3902_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3900_, v___x_3901_);
if (v___x_3902_ == 0)
{
v___y_3895_ = v_as_3870_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_array_fswap(v_as_3870_, v_lo_3871_, v_mid_3887_);
v___y_3895_ = v___x_3903_;
goto v___jp_3894_;
}
v___jp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3890_ = lean_array_fget_borrowed(v___y_3889_, v_mid_3887_);
v___x_3891_ = lean_array_fget_borrowed(v___y_3889_, v_hi_3872_);
v___x_3892_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3890_, v___x_3891_);
if (v___x_3892_ == 0)
{
lean_dec(v_mid_3887_);
v___y_3874_ = v___y_3889_;
goto v___jp_3873_;
}
else
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_array_fswap(v___y_3889_, v_mid_3887_, v_hi_3872_);
lean_dec(v_mid_3887_);
v___y_3874_ = v___x_3893_;
goto v___jp_3873_;
}
}
v___jp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3896_ = lean_array_fget_borrowed(v___y_3895_, v_hi_3872_);
v___x_3897_ = lean_array_fget_borrowed(v___y_3895_, v_lo_3871_);
v___x_3898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
v___y_3889_ = v___y_3895_;
goto v___jp_3888_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_array_fswap(v___y_3895_, v_lo_3871_, v_hi_3872_);
v___y_3889_ = v___x_3899_;
goto v___jp_3888_;
}
}
}
v___jp_3873_:
{
lean_object* v_pivot_3875_; lean_object* v___x_3876_; lean_object* v_fst_3877_; lean_object* v_snd_3878_; uint8_t v___x_3879_; 
v_pivot_3875_ = lean_array_fget(v___y_3874_, v_hi_3872_);
lean_inc_n(v_lo_3871_, 2);
v___x_3876_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3872_, v_pivot_3875_, v___y_3874_, v_lo_3871_, v_lo_3871_);
lean_dec(v_pivot_3875_);
v_fst_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_fst_3877_);
v_snd_3878_ = lean_ctor_get(v___x_3876_, 1);
lean_inc(v_snd_3878_);
lean_dec_ref(v___x_3876_);
v___x_3879_ = lean_nat_dec_le(v_hi_3872_, v_fst_3877_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3869_, v_snd_3878_, v_lo_3871_, v_fst_3877_);
v___x_3881_ = lean_unsigned_to_nat(1u);
v___x_3882_ = lean_nat_add(v_fst_3877_, v___x_3881_);
lean_dec(v_fst_3877_);
v_as_3870_ = v___x_3880_;
v_lo_3871_ = v___x_3882_;
goto _start;
}
else
{
lean_dec(v_fst_3877_);
lean_dec(v_lo_3871_);
return v_snd_3878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3904_, lean_object* v_as_3905_, lean_object* v_lo_3906_, lean_object* v_hi_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3904_, v_as_3905_, v_lo_3906_, v_hi_3907_);
lean_dec(v_hi_3907_);
lean_dec(v_n_3904_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3909_, lean_object* v_hyps_3910_){
_start:
{
lean_object* v___y_3912_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v_hyps_3918_; lean_object* v___x_3919_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_sz_3916_ = lean_array_size(v_hyps_3910_);
v___x_3917_ = ((size_t)0ULL);
v_hyps_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3909_, v_sz_3916_, v___x_3917_, v_hyps_3910_);
v___x_3919_ = lean_array_get_size(v_hyps_3918_);
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = lean_nat_dec_eq(v___x_3919_, v___x_3924_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___y_3929_; uint8_t v___x_3931_; 
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_sub(v___x_3919_, v___x_3926_);
v___x_3931_ = lean_nat_dec_le(v___x_3924_, v___x_3927_);
if (v___x_3931_ == 0)
{
lean_inc(v___x_3927_);
v___y_3929_ = v___x_3927_;
goto v___jp_3928_;
}
else
{
v___y_3929_ = v___x_3924_;
goto v___jp_3928_;
}
v___jp_3928_:
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_nat_dec_le(v___y_3929_, v___x_3927_);
if (v___x_3930_ == 0)
{
lean_dec(v___x_3927_);
lean_inc(v___y_3929_);
v___y_3921_ = v___y_3929_;
v___y_3922_ = v___y_3929_;
goto v___jp_3920_;
}
else
{
v___y_3921_ = v___y_3929_;
v___y_3922_ = v___x_3927_;
goto v___jp_3920_;
}
}
}
else
{
v___y_3912_ = v_hyps_3918_;
goto v___jp_3911_;
}
v___jp_3911_:
{
size_t v_sz_3913_; size_t v___x_3914_; lean_object* v___x_3915_; 
v_sz_3913_ = lean_array_size(v___y_3912_);
v___x_3914_ = ((size_t)0ULL);
v___x_3915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3913_, v___x_3914_, v___y_3912_);
return v___x_3915_;
}
v___jp_3920_:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3919_, v_hyps_3918_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
v___y_3912_ = v___x_3923_;
goto v___jp_3911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3932_, lean_object* v_hyps_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3932_, v_hyps_3933_);
lean_dec_ref(v_lctx_3932_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3935_, lean_object* v_as_3936_, lean_object* v_lo_3937_, lean_object* v_hi_3938_, lean_object* v_w_3939_, lean_object* v_hlo_3940_, lean_object* v_hhi_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3935_, v_as_3936_, v_lo_3937_, v_hi_3938_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3943_, lean_object* v_as_3944_, lean_object* v_lo_3945_, lean_object* v_hi_3946_, lean_object* v_w_3947_, lean_object* v_hlo_3948_, lean_object* v_hhi_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3943_, v_as_3944_, v_lo_3945_, v_hi_3946_, v_w_3947_, v_hlo_3948_, v_hhi_3949_);
lean_dec(v_hi_3946_);
lean_dec(v_n_3943_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3951_, lean_object* v_lo_3952_, lean_object* v_hi_3953_, lean_object* v_hhi_3954_, lean_object* v_pivot_3955_, lean_object* v_as_3956_, lean_object* v_i_3957_, lean_object* v_k_3958_, lean_object* v_ilo_3959_, lean_object* v_ik_3960_, lean_object* v_w_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3953_, v_pivot_3955_, v_as_3956_, v_i_3957_, v_k_3958_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_3963_, lean_object* v_lo_3964_, lean_object* v_hi_3965_, lean_object* v_hhi_3966_, lean_object* v_pivot_3967_, lean_object* v_as_3968_, lean_object* v_i_3969_, lean_object* v_k_3970_, lean_object* v_ilo_3971_, lean_object* v_ik_3972_, lean_object* v_w_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_3963_, v_lo_3964_, v_hi_3965_, v_hhi_3966_, v_pivot_3967_, v_as_3968_, v_i_3969_, v_k_3970_, v_ilo_3971_, v_ik_3972_, v_w_3973_);
lean_dec_ref(v_pivot_3967_);
lean_dec(v_hi_3965_);
lean_dec(v_lo_3964_);
lean_dec(v_n_3963_);
return v_res_3974_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3975_, lean_object* v_x_3976_){
_start:
{
if (lean_obj_tag(v_x_3976_) == 0)
{
uint8_t v___x_3977_; 
v___x_3977_ = 0;
return v___x_3977_;
}
else
{
lean_object* v_key_3978_; lean_object* v_tail_3979_; uint8_t v___x_3980_; 
v_key_3978_ = lean_ctor_get(v_x_3976_, 0);
v_tail_3979_ = lean_ctor_get(v_x_3976_, 2);
v___x_3980_ = lean_name_eq(v_key_3978_, v_a_3975_);
if (v___x_3980_ == 0)
{
v_x_3976_ = v_tail_3979_;
goto _start;
}
else
{
return v___x_3980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3982_, lean_object* v_x_3983_){
_start:
{
uint8_t v_res_3984_; lean_object* v_r_3985_; 
v_res_3984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3982_, v_x_3983_);
lean_dec(v_x_3983_);
lean_dec(v_a_3982_);
v_r_3985_ = lean_box(v_res_3984_);
return v_r_3985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3986_, lean_object* v_x_3987_){
_start:
{
if (lean_obj_tag(v_x_3987_) == 0)
{
return v_x_3987_;
}
else
{
lean_object* v_key_3988_; lean_object* v_value_3989_; lean_object* v_tail_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3999_; 
v_key_3988_ = lean_ctor_get(v_x_3987_, 0);
v_value_3989_ = lean_ctor_get(v_x_3987_, 1);
v_tail_3990_ = lean_ctor_get(v_x_3987_, 2);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_x_3987_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3992_ = v_x_3987_;
v_isShared_3993_ = v_isSharedCheck_3999_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_tail_3990_);
lean_inc(v_value_3989_);
lean_inc(v_key_3988_);
lean_dec(v_x_3987_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3999_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_name_eq(v_key_3988_, v_a_3986_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3986_, v_tail_3990_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 2, v___x_3995_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_key_3988_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_value_3989_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_del_object(v___x_3992_);
lean_dec(v_value_3989_);
lean_dec(v_key_3988_);
return v_tail_3990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4000_, lean_object* v_x_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4000_, v_x_4001_);
lean_dec(v_a_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_size_4005_; lean_object* v_buckets_4006_; lean_object* v___x_4007_; uint64_t v___y_4009_; 
v_size_4005_ = lean_ctor_get(v_m_4003_, 0);
v_buckets_4006_ = lean_ctor_get(v_m_4003_, 1);
v___x_4007_ = lean_array_get_size(v_buckets_4006_);
if (lean_obj_tag(v_a_4004_) == 0)
{
uint64_t v___x_4038_; 
v___x_4038_ = 1723ULL;
v___y_4009_ = v___x_4038_;
goto v___jp_4008_;
}
else
{
uint64_t v_hash_4039_; 
v_hash_4039_ = lean_ctor_get_uint64(v_a_4004_, sizeof(void*)*2);
v___y_4009_ = v_hash_4039_;
goto v___jp_4008_;
}
v___jp_4008_:
{
uint64_t v___x_4010_; uint64_t v___x_4011_; uint64_t v_fold_4012_; uint64_t v___x_4013_; uint64_t v___x_4014_; uint64_t v___x_4015_; size_t v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; size_t v___x_4019_; size_t v___x_4020_; lean_object* v_bkt_4021_; uint8_t v___x_4022_; 
v___x_4010_ = 32ULL;
v___x_4011_ = lean_uint64_shift_right(v___y_4009_, v___x_4010_);
v_fold_4012_ = lean_uint64_xor(v___y_4009_, v___x_4011_);
v___x_4013_ = 16ULL;
v___x_4014_ = lean_uint64_shift_right(v_fold_4012_, v___x_4013_);
v___x_4015_ = lean_uint64_xor(v_fold_4012_, v___x_4014_);
v___x_4016_ = lean_uint64_to_usize(v___x_4015_);
v___x_4017_ = lean_usize_of_nat(v___x_4007_);
v___x_4018_ = ((size_t)1ULL);
v___x_4019_ = lean_usize_sub(v___x_4017_, v___x_4018_);
v___x_4020_ = lean_usize_land(v___x_4016_, v___x_4019_);
v_bkt_4021_ = lean_array_uget_borrowed(v_buckets_4006_, v___x_4020_);
v___x_4022_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4004_, v_bkt_4021_);
if (v___x_4022_ == 0)
{
return v_m_4003_;
}
else
{
lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4035_; 
lean_inc(v_bkt_4021_);
lean_inc_ref(v_buckets_4006_);
lean_inc(v_size_4005_);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_m_4003_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; lean_object* v_unused_4037_; 
v_unused_4036_ = lean_ctor_get(v_m_4003_, 1);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_m_4003_, 0);
lean_dec(v_unused_4037_);
v___x_4024_ = v_m_4003_;
v_isShared_4025_ = v_isSharedCheck_4035_;
goto v_resetjp_4023_;
}
else
{
lean_dec(v_m_4003_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4035_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v_buckets_x27_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4026_ = lean_box(0);
v_buckets_x27_4027_ = lean_array_uset(v_buckets_4006_, v___x_4020_, v___x_4026_);
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_sub(v_size_4005_, v___x_4028_);
lean_dec(v_size_4005_);
v___x_4030_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4004_, v_bkt_4021_);
v___x_4031_ = lean_array_uset(v_buckets_x27_4027_, v___x_4020_, v___x_4030_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 1, v___x_4031_);
lean_ctor_set(v___x_4024_, 0, v___x_4029_);
v___x_4033_ = v___x_4024_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4040_, v_a_4041_);
lean_dec(v_a_4041_);
return v_res_4042_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_buckets_4045_; lean_object* v___x_4046_; uint64_t v___y_4048_; 
v_buckets_4045_ = lean_ctor_get(v_m_4043_, 1);
v___x_4046_ = lean_array_get_size(v_buckets_4045_);
if (lean_obj_tag(v_a_4044_) == 0)
{
uint64_t v___x_4062_; 
v___x_4062_ = 1723ULL;
v___y_4048_ = v___x_4062_;
goto v___jp_4047_;
}
else
{
uint64_t v_hash_4063_; 
v_hash_4063_ = lean_ctor_get_uint64(v_a_4044_, sizeof(void*)*2);
v___y_4048_ = v_hash_4063_;
goto v___jp_4047_;
}
v___jp_4047_:
{
uint64_t v___x_4049_; uint64_t v___x_4050_; uint64_t v_fold_4051_; uint64_t v___x_4052_; uint64_t v___x_4053_; uint64_t v___x_4054_; size_t v___x_4055_; size_t v___x_4056_; size_t v___x_4057_; size_t v___x_4058_; size_t v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4049_ = 32ULL;
v___x_4050_ = lean_uint64_shift_right(v___y_4048_, v___x_4049_);
v_fold_4051_ = lean_uint64_xor(v___y_4048_, v___x_4050_);
v___x_4052_ = 16ULL;
v___x_4053_ = lean_uint64_shift_right(v_fold_4051_, v___x_4052_);
v___x_4054_ = lean_uint64_xor(v_fold_4051_, v___x_4053_);
v___x_4055_ = lean_uint64_to_usize(v___x_4054_);
v___x_4056_ = lean_usize_of_nat(v___x_4046_);
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_sub(v___x_4056_, v___x_4057_);
v___x_4059_ = lean_usize_land(v___x_4055_, v___x_4058_);
v___x_4060_ = lean_array_uget_borrowed(v_buckets_4045_, v___x_4059_);
v___x_4061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4044_, v___x_4060_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4064_, lean_object* v_a_4065_){
_start:
{
uint8_t v_res_4066_; lean_object* v_r_4067_; 
v_res_4066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4064_, v_a_4065_);
lean_dec(v_a_4065_);
lean_dec_ref(v_m_4064_);
v_r_4067_ = lean_box(v_res_4066_);
return v_r_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4068_, lean_object* v_as_4069_, size_t v_i_4070_, size_t v_stop_4071_, lean_object* v_b_4072_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = lean_usize_dec_eq(v_i_4070_, v_stop_4071_);
if (v___x_4073_ == 0)
{
size_t v___x_4074_; size_t v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((size_t)1ULL);
v___x_4075_ = lean_usize_sub(v_i_4070_, v___x_4074_);
v___x_4076_ = lean_array_uget(v_as_4069_, v___x_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
v_i_4070_ = v___x_4075_;
goto _start;
}
else
{
lean_object* v_val_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4112_; 
v_val_4078_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4080_ = v___x_4076_;
v_isShared_4081_ = v_isSharedCheck_4112_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_val_4078_);
lean_dec(v___x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4112_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v_fst_4082_; lean_object* v_snd_4083_; lean_object* v___y_4085_; lean_object* v___y_4101_; lean_object* v_size_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v_fst_4082_ = lean_ctor_get(v_b_4072_, 0);
v_snd_4083_ = lean_ctor_get(v_b_4072_, 1);
v_size_4107_ = lean_ctor_get(v_fst_4082_, 0);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_nat_dec_eq(v_size_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v_index_4110_; 
v_index_4110_ = lean_ctor_get(v_val_4078_, 0);
lean_inc(v_index_4110_);
v___y_4101_ = v_index_4110_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4111_; 
lean_inc(v_snd_4083_);
lean_del_object(v___x_4080_);
lean_dec(v_val_4078_);
lean_dec_ref(v_b_4072_);
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_snd_4083_);
return v___x_4111_;
}
v___jp_4084_:
{
uint8_t v___x_4086_; 
v___x_4086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4082_, v___y_4085_);
if (v___x_4086_ == 0)
{
lean_dec(v___y_4085_);
lean_dec(v_val_4078_);
v_i_4070_ = v___x_4075_;
goto _start;
}
else
{
lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4097_; 
lean_inc(v_snd_4083_);
lean_inc(v_fst_4082_);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_b_4072_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; lean_object* v_unused_4099_; 
v_unused_4098_ = lean_ctor_get(v_b_4072_, 1);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_b_4072_, 0);
lean_dec(v_unused_4099_);
v___x_4089_ = v_b_4072_;
v_isShared_4090_ = v_isSharedCheck_4097_;
goto v_resetjp_4088_;
}
else
{
lean_dec(v_b_4072_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4097_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4091_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4082_, v___y_4085_);
lean_dec(v___y_4085_);
v___x_4092_ = lean_array_push(v_snd_4083_, v_val_4078_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 1, v___x_4092_);
lean_ctor_set(v___x_4089_, 0, v___x_4091_);
v___x_4094_ = v___x_4089_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
v_i_4070_ = v___x_4075_;
v_b_4072_ = v___x_4094_;
goto _start;
}
}
}
}
v___jp_4100_:
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_nat_dec_lt(v___y_4101_, v_start_4068_);
lean_dec(v___y_4101_);
if (v___x_4102_ == 0)
{
lean_object* v_userName_4103_; 
lean_del_object(v___x_4080_);
v_userName_4103_ = lean_ctor_get(v_val_4078_, 2);
lean_inc(v_userName_4103_);
v___y_4085_ = v_userName_4103_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4105_; 
lean_inc(v_snd_4083_);
lean_dec(v_val_4078_);
lean_dec_ref(v_b_4072_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set_tag(v___x_4080_, 0);
lean_ctor_set(v___x_4080_, 0, v_snd_4083_);
v___x_4105_ = v___x_4080_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_snd_4083_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
}
else
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_b_4072_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4114_, lean_object* v_as_4115_, lean_object* v_i_4116_, lean_object* v_stop_4117_, lean_object* v_b_4118_){
_start:
{
size_t v_i_boxed_4119_; size_t v_stop_boxed_4120_; lean_object* v_res_4121_; 
v_i_boxed_4119_ = lean_unbox_usize(v_i_4116_);
lean_dec(v_i_4116_);
v_stop_boxed_4120_ = lean_unbox_usize(v_stop_4117_);
lean_dec(v_stop_4117_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4114_, v_as_4115_, v_i_boxed_4119_, v_stop_boxed_4120_, v_b_4118_);
lean_dec_ref(v_as_4115_);
lean_dec(v_start_4114_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4122_, lean_object* v_x_4123_, lean_object* v_x_4124_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v_cs_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4138_; 
v_cs_4125_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4127_ = v_x_4123_;
v_isShared_4128_ = v_isSharedCheck_4138_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_cs_4125_);
lean_dec(v_x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4138_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v___x_4129_ = lean_array_get_size(v_cs_4125_);
v___x_4130_ = lean_unsigned_to_nat(0u);
v___x_4131_ = lean_nat_dec_lt(v___x_4130_, v___x_4129_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4133_; 
lean_dec_ref(v_cs_4125_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 1);
lean_ctor_set(v___x_4127_, 0, v_x_4124_);
v___x_4133_ = v___x_4127_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_x_4124_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
else
{
size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
lean_del_object(v___x_4127_);
v___x_4135_ = lean_usize_of_nat(v___x_4129_);
v___x_4136_ = ((size_t)0ULL);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4122_, v_cs_4125_, v___x_4135_, v___x_4136_, v_x_4124_);
lean_dec_ref(v_cs_4125_);
return v___x_4137_;
}
}
}
else
{
lean_object* v_vs_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4152_; 
v_vs_4139_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4141_ = v_x_4123_;
v_isShared_4142_ = v_isSharedCheck_4152_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_vs_4139_);
lean_dec(v_x_4123_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4152_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v___x_4143_ = lean_array_get_size(v_vs_4139_);
v___x_4144_ = lean_unsigned_to_nat(0u);
v___x_4145_ = lean_nat_dec_lt(v___x_4144_, v___x_4143_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4147_; 
lean_dec_ref(v_vs_4139_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v_x_4124_);
v___x_4147_ = v___x_4141_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_x_4124_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
size_t v___x_4149_; size_t v___x_4150_; lean_object* v___x_4151_; 
lean_del_object(v___x_4141_);
v___x_4149_ = lean_usize_of_nat(v___x_4143_);
v___x_4150_ = ((size_t)0ULL);
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4122_, v_vs_4139_, v___x_4149_, v___x_4150_, v_x_4124_);
lean_dec_ref(v_vs_4139_);
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4153_, lean_object* v_as_4154_, size_t v_i_4155_, size_t v_stop_4156_, lean_object* v_b_4157_){
_start:
{
uint8_t v___x_4158_; 
v___x_4158_ = lean_usize_dec_eq(v_i_4155_, v_stop_4156_);
if (v___x_4158_ == 0)
{
size_t v___x_4159_; size_t v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4159_ = ((size_t)1ULL);
v___x_4160_ = lean_usize_sub(v_i_4155_, v___x_4159_);
v___x_4161_ = lean_array_uget_borrowed(v_as_4154_, v___x_4160_);
lean_inc(v___x_4161_);
v___x_4162_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4153_, v___x_4161_, v_b_4157_);
if (lean_obj_tag(v___x_4162_) == 0)
{
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v_i_4155_ = v___x_4160_;
v_b_4157_ = v_a_4163_;
goto _start;
}
}
else
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_b_4157_);
return v___x_4165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4166_, lean_object* v_as_4167_, lean_object* v_i_4168_, lean_object* v_stop_4169_, lean_object* v_b_4170_){
_start:
{
size_t v_i_boxed_4171_; size_t v_stop_boxed_4172_; lean_object* v_res_4173_; 
v_i_boxed_4171_ = lean_unbox_usize(v_i_4168_);
lean_dec(v_i_4168_);
v_stop_boxed_4172_ = lean_unbox_usize(v_stop_4169_);
lean_dec(v_stop_4169_);
v_res_4173_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4166_, v_as_4167_, v_i_boxed_4171_, v_stop_boxed_4172_, v_b_4170_);
lean_dec_ref(v_as_4167_);
lean_dec(v_start_4166_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4174_, lean_object* v_x_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4174_, v_x_4175_, v_x_4176_);
lean_dec(v_start_4174_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4178_, lean_object* v_t_4179_, lean_object* v_init_4180_){
_start:
{
lean_object* v_root_4181_; lean_object* v_tail_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_root_4181_ = lean_ctor_get(v_t_4179_, 0);
lean_inc_ref(v_root_4181_);
v_tail_4182_ = lean_ctor_get(v_t_4179_, 1);
lean_inc_ref(v_tail_4182_);
lean_dec_ref(v_t_4179_);
v___x_4183_ = lean_array_get_size(v_tail_4182_);
v___x_4184_ = lean_unsigned_to_nat(0u);
v___x_4185_ = lean_nat_dec_lt(v___x_4184_, v___x_4183_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; 
lean_dec_ref(v_tail_4182_);
v___x_4186_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4178_, v_root_4181_, v_init_4180_);
return v___x_4186_;
}
else
{
size_t v___x_4187_; size_t v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = lean_usize_of_nat(v___x_4183_);
v___x_4188_ = ((size_t)0ULL);
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4178_, v_tail_4182_, v___x_4187_, v___x_4188_, v_init_4180_);
lean_dec_ref(v_tail_4182_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref(v_root_4181_);
return v___x_4189_;
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4178_, v_root_4181_, v_a_4190_);
return v___x_4191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4192_, lean_object* v_t_4193_, lean_object* v_init_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4192_, v_t_4193_, v_init_4194_);
lean_dec(v_start_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4196_, lean_object* v_lctx_4197_, lean_object* v_init_4198_){
_start:
{
lean_object* v_decls_4199_; lean_object* v___x_4200_; 
v_decls_4199_ = lean_ctor_get(v_lctx_4197_, 1);
lean_inc_ref(v_decls_4199_);
lean_dec_ref(v_lctx_4197_);
v___x_4200_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4196_, v_decls_4199_, v_init_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4201_, lean_object* v_lctx_4202_, lean_object* v_init_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4201_, v_lctx_4202_, v_init_4203_);
lean_dec(v_start_4201_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4207_, lean_object* v_userNames_4208_, lean_object* v_start_4209_){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4210_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v_userNames_4208_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4209_, v_lctx_4207_, v___x_4211_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = l_Array_reverse___redArg(v_a_4213_);
return v___x_4214_;
}
else
{
lean_object* v_a_4215_; lean_object* v_snd_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_a_4215_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4212_, 1);
v_snd_4216_ = lean_ctor_get(v_a_4215_, 1);
lean_inc(v_snd_4216_);
lean_dec(v_a_4215_);
v___x_4217_ = l_Array_reverse___redArg(v_snd_4216_);
v___x_4218_ = l_Array_reverse___redArg(v___x_4217_);
return v___x_4218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4219_, lean_object* v_userNames_4220_, lean_object* v_start_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4219_, v_userNames_4220_, v_start_4221_);
lean_dec(v_start_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4223_, lean_object* v_lctx_4224_, lean_object* v_userNames_4225_, lean_object* v_start_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4224_, v_userNames_4225_, v_start_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4228_, lean_object* v_lctx_4229_, lean_object* v_userNames_4230_, lean_object* v_start_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4228_, v_lctx_4229_, v_userNames_4230_, v_start_4231_);
lean_dec(v_start_4231_);
return v_res_4232_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4233_, lean_object* v_m_4234_, lean_object* v_a_4235_){
_start:
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4234_, v_a_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4237_, lean_object* v_m_4238_, lean_object* v_a_4239_){
_start:
{
uint8_t v_res_4240_; lean_object* v_r_4241_; 
v_res_4240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4237_, v_m_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_m_4238_);
v_r_4241_ = lean_box(v_res_4240_);
return v_r_4241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4242_, lean_object* v_m_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4243_, v_a_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4246_, lean_object* v_m_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4246_, v_m_4247_, v_a_4248_);
lean_dec(v_a_4248_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4250_, lean_object* v_start_4251_, lean_object* v_lctx_4252_, lean_object* v_init_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4251_, v_lctx_4252_, v_init_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4255_, lean_object* v_start_4256_, lean_object* v_lctx_4257_, lean_object* v_init_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4255_, v_start_4256_, v_lctx_4257_, v_init_4258_);
lean_dec(v_start_4256_);
return v_res_4259_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4260_, lean_object* v_a_4261_, lean_object* v_x_4262_){
_start:
{
uint8_t v___x_4263_; 
v___x_4263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4261_, v_x_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4264_, lean_object* v_a_4265_, lean_object* v_x_4266_){
_start:
{
uint8_t v_res_4267_; lean_object* v_r_4268_; 
v_res_4267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4264_, v_a_4265_, v_x_4266_);
lean_dec(v_x_4266_);
lean_dec(v_a_4265_);
v_r_4268_ = lean_box(v_res_4267_);
return v_r_4268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4269_, lean_object* v_a_4270_, lean_object* v_x_4271_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4270_, v_x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4273_, lean_object* v_a_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4273_, v_a_4274_, v_x_4275_);
lean_dec(v_a_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4277_, lean_object* v_start_4278_, lean_object* v_t_4279_, lean_object* v_init_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4278_, v_t_4279_, v_init_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4282_, lean_object* v_start_4283_, lean_object* v_t_4284_, lean_object* v_init_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4282_, v_start_4283_, v_t_4284_, v_init_4285_);
lean_dec(v_start_4283_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4287_, lean_object* v_start_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4288_, v_x_4289_, v_x_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4292_, lean_object* v_start_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4292_, v_start_4293_, v_x_4294_, v_x_4295_);
lean_dec(v_start_4293_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4297_, lean_object* v_start_4298_, lean_object* v_as_4299_, size_t v_i_4300_, size_t v_stop_4301_, lean_object* v_b_4302_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4298_, v_as_4299_, v_i_4300_, v_stop_4301_, v_b_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4304_, lean_object* v_start_4305_, lean_object* v_as_4306_, lean_object* v_i_4307_, lean_object* v_stop_4308_, lean_object* v_b_4309_){
_start:
{
size_t v_i_boxed_4310_; size_t v_stop_boxed_4311_; lean_object* v_res_4312_; 
v_i_boxed_4310_ = lean_unbox_usize(v_i_4307_);
lean_dec(v_i_4307_);
v_stop_boxed_4311_ = lean_unbox_usize(v_stop_4308_);
lean_dec(v_stop_4308_);
v_res_4312_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4304_, v_start_4305_, v_as_4306_, v_i_boxed_4310_, v_stop_boxed_4311_, v_b_4309_);
lean_dec_ref(v_as_4306_);
lean_dec(v_start_4305_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4313_, lean_object* v_start_4314_, lean_object* v_as_4315_, size_t v_i_4316_, size_t v_stop_4317_, lean_object* v_b_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4314_, v_as_4315_, v_i_4316_, v_stop_4317_, v_b_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4320_, lean_object* v_start_4321_, lean_object* v_as_4322_, lean_object* v_i_4323_, lean_object* v_stop_4324_, lean_object* v_b_4325_){
_start:
{
size_t v_i_boxed_4326_; size_t v_stop_boxed_4327_; lean_object* v_res_4328_; 
v_i_boxed_4326_ = lean_unbox_usize(v_i_4323_);
lean_dec(v_i_4323_);
v_stop_boxed_4327_ = lean_unbox_usize(v_stop_4324_);
lean_dec(v_stop_4324_);
v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4320_, v_start_4321_, v_as_4322_, v_i_boxed_4326_, v_stop_boxed_4327_, v_b_4325_);
lean_dec_ref(v_as_4322_);
lean_dec(v_start_4321_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4329_, lean_object* v_inst_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_apply_2(v_inst_4329_, lean_box(0), v_inst_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4332_, lean_object* v_n_4333_, lean_object* v_inst_4334_, lean_object* v_inst_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = lean_apply_2(v_inst_4334_, lean_box(0), v_inst_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4337_, lean_object* v_d_x3f_4338_, lean_object* v_b_4339_){
_start:
{
if (lean_obj_tag(v_d_x3f_4338_) == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4340_, 0, v_b_4339_);
v___x_4341_ = lean_apply_2(v_toPure_4337_, lean_box(0), v___x_4340_);
return v___x_4341_;
}
else
{
lean_object* v_val_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4357_; 
v_val_4342_ = lean_ctor_get(v_d_x3f_4338_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_d_x3f_4338_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4344_ = v_d_x3f_4338_;
v_isShared_4345_ = v_isSharedCheck_4357_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_val_4342_);
lean_dec(v_d_x3f_4338_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4357_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
uint8_t v___x_4346_; 
v___x_4346_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4342_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4347_ = l_Lean_LocalDecl_toExpr(v_val_4342_);
v___x_4348_ = lean_array_push(v_b_4339_, v___x_4347_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4348_);
v___x_4350_ = v___x_4344_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_apply_2(v_toPure_4337_, lean_box(0), v___x_4350_);
return v___x_4351_;
}
}
else
{
lean_object* v___x_4354_; 
lean_dec(v_val_4342_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_b_4339_);
v___x_4354_ = v___x_4344_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_b_4339_);
v___x_4354_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_apply_2(v_toPure_4337_, lean_box(0), v___x_4354_);
return v___x_4355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4358_, lean_object* v_____s_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_apply_2(v_toPure_4358_, lean_box(0), v_____s_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4361_, lean_object* v_hs_4362_, lean_object* v___f_4363_, lean_object* v_toBind_4364_, lean_object* v___f_4365_, lean_object* v_____do__lift_4366_){
_start:
{
lean_object* v_decls_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_decls_4367_ = lean_ctor_get(v_____do__lift_4366_, 1);
v___x_4368_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4361_, v_decls_4367_, v_hs_4362_, v___f_4363_);
v___x_4369_ = lean_apply_4(v_toBind_4364_, lean_box(0), lean_box(0), v___x_4368_, v___f_4365_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4370_, lean_object* v_hs_4371_, lean_object* v___f_4372_, lean_object* v_toBind_4373_, lean_object* v___f_4374_, lean_object* v_____do__lift_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4370_, v_hs_4371_, v___f_4372_, v_toBind_4373_, v___f_4374_, v_____do__lift_4375_);
lean_dec_ref(v_____do__lift_4375_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4379_, lean_object* v_inst_4380_){
_start:
{
lean_object* v_toApplicative_4381_; lean_object* v_toBind_4382_; lean_object* v_toPure_4383_; lean_object* v_hs_4384_; lean_object* v___f_4385_; lean_object* v___f_4386_; lean_object* v___f_4387_; lean_object* v___x_4388_; 
v_toApplicative_4381_ = lean_ctor_get(v_inst_4379_, 0);
v_toBind_4382_ = lean_ctor_get(v_inst_4379_, 1);
lean_inc_n(v_toBind_4382_, 2);
v_toPure_4383_ = lean_ctor_get(v_toApplicative_4381_, 1);
v_hs_4384_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4383_, 2);
v___f_4385_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4385_, 0, v_toPure_4383_);
v___f_4386_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4386_, 0, v_toPure_4383_);
v___f_4387_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4387_, 0, v_inst_4379_);
lean_closure_set(v___f_4387_, 1, v_hs_4384_);
lean_closure_set(v___f_4387_, 2, v___f_4385_);
lean_closure_set(v___f_4387_, 3, v_toBind_4382_);
lean_closure_set(v___f_4387_, 4, v___f_4386_);
v___x_4388_ = lean_apply_4(v_toBind_4382_, lean_box(0), lean_box(0), v_inst_4380_, v___f_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4389_, lean_object* v_inst_4390_, lean_object* v_inst_4391_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_getLocalHyps___redArg(v_inst_4390_, v_inst_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4393_, lean_object* v_e_4394_, lean_object* v_d_4395_){
_start:
{
lean_object* v___y_4397_; lean_object* v_fvarId_4429_; 
v_fvarId_4429_ = lean_ctor_get(v_d_4395_, 1);
lean_inc(v_fvarId_4429_);
v___y_4397_ = v_fvarId_4429_;
goto v___jp_4396_;
v___jp_4396_:
{
uint8_t v___x_4398_; 
v___x_4398_ = l_Lean_instBEqFVarId_beq(v___y_4397_, v_fvarId_4393_);
lean_dec(v___y_4397_);
if (v___x_4398_ == 0)
{
if (lean_obj_tag(v_d_4395_) == 0)
{
lean_object* v_index_4399_; lean_object* v_fvarId_4400_; lean_object* v_userName_4401_; lean_object* v_type_4402_; uint8_t v_bi_4403_; uint8_t v_kind_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4412_; 
v_index_4399_ = lean_ctor_get(v_d_4395_, 0);
v_fvarId_4400_ = lean_ctor_get(v_d_4395_, 1);
v_userName_4401_ = lean_ctor_get(v_d_4395_, 2);
v_type_4402_ = lean_ctor_get(v_d_4395_, 3);
v_bi_4403_ = lean_ctor_get_uint8(v_d_4395_, sizeof(void*)*4);
v_kind_4404_ = lean_ctor_get_uint8(v_d_4395_, sizeof(void*)*4 + 1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_d_4395_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4406_ = v_d_4395_;
v_isShared_4407_ = v_isSharedCheck_4412_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_type_4402_);
lean_inc(v_userName_4401_);
lean_inc(v_fvarId_4400_);
lean_inc(v_index_4399_);
lean_dec(v_d_4395_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4412_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4408_ = l_Lean_Expr_replaceFVarId(v_type_4402_, v_fvarId_4393_, v_e_4394_);
lean_dec_ref(v_type_4402_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 3, v___x_4408_);
v___x_4410_ = v___x_4406_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_index_4399_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_fvarId_4400_);
lean_ctor_set(v_reuseFailAlloc_4411_, 2, v_userName_4401_);
lean_ctor_set(v_reuseFailAlloc_4411_, 3, v___x_4408_);
lean_ctor_set_uint8(v_reuseFailAlloc_4411_, sizeof(void*)*4, v_bi_4403_);
lean_ctor_set_uint8(v_reuseFailAlloc_4411_, sizeof(void*)*4 + 1, v_kind_4404_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
else
{
lean_object* v_index_4413_; lean_object* v_fvarId_4414_; lean_object* v_userName_4415_; lean_object* v_type_4416_; lean_object* v_value_4417_; uint8_t v_nondep_4418_; uint8_t v_kind_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4428_; 
v_index_4413_ = lean_ctor_get(v_d_4395_, 0);
v_fvarId_4414_ = lean_ctor_get(v_d_4395_, 1);
v_userName_4415_ = lean_ctor_get(v_d_4395_, 2);
v_type_4416_ = lean_ctor_get(v_d_4395_, 3);
v_value_4417_ = lean_ctor_get(v_d_4395_, 4);
v_nondep_4418_ = lean_ctor_get_uint8(v_d_4395_, sizeof(void*)*5);
v_kind_4419_ = lean_ctor_get_uint8(v_d_4395_, sizeof(void*)*5 + 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_d_4395_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4421_ = v_d_4395_;
v_isShared_4422_ = v_isSharedCheck_4428_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_value_4417_);
lean_inc(v_type_4416_);
lean_inc(v_userName_4415_);
lean_inc(v_fvarId_4414_);
lean_inc(v_index_4413_);
lean_dec(v_d_4395_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4428_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
lean_inc(v_fvarId_4393_);
v___x_4423_ = l_Lean_Expr_replaceFVarId(v_type_4416_, v_fvarId_4393_, v_e_4394_);
lean_dec_ref(v_type_4416_);
v___x_4424_ = l_Lean_Expr_replaceFVarId(v_value_4417_, v_fvarId_4393_, v_e_4394_);
lean_dec_ref(v_value_4417_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 4, v___x_4424_);
lean_ctor_set(v___x_4421_, 3, v___x_4423_);
v___x_4426_ = v___x_4421_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_index_4413_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_fvarId_4414_);
lean_ctor_set(v_reuseFailAlloc_4427_, 2, v_userName_4415_);
lean_ctor_set(v_reuseFailAlloc_4427_, 3, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4427_, 4, v___x_4424_);
lean_ctor_set_uint8(v_reuseFailAlloc_4427_, sizeof(void*)*5, v_nondep_4418_);
lean_ctor_set_uint8(v_reuseFailAlloc_4427_, sizeof(void*)*5 + 1, v_kind_4419_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
lean_dec(v_fvarId_4393_);
return v_d_4395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4430_, lean_object* v_e_4431_, lean_object* v_d_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4430_, v_e_4431_, v_d_4432_);
lean_dec_ref(v_e_4431_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4434_, lean_object* v_e_4435_, lean_object* v_x_4436_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4434_, v_e_4435_, v_x_4436_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4438_, lean_object* v_e_4439_, lean_object* v_x_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4438_, v_e_4439_, v_x_4440_);
lean_dec_ref(v_e_4439_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4442_, lean_object* v_e_4443_, size_t v_sz_4444_, size_t v_i_4445_, lean_object* v_bs_4446_){
_start:
{
uint8_t v___x_4447_; 
v___x_4447_ = lean_usize_dec_lt(v_i_4445_, v_sz_4444_);
if (v___x_4447_ == 0)
{
lean_dec(v_fvarId_4442_);
return v_bs_4446_;
}
else
{
lean_object* v_v_4448_; lean_object* v___x_4449_; lean_object* v_bs_x27_4450_; lean_object* v___y_4452_; 
v_v_4448_ = lean_array_uget(v_bs_4446_, v_i_4445_);
v___x_4449_ = lean_unsigned_to_nat(0u);
v_bs_x27_4450_ = lean_array_uset(v_bs_4446_, v_i_4445_, v___x_4449_);
if (lean_obj_tag(v_v_4448_) == 0)
{
v___y_4452_ = v_v_4448_;
goto v___jp_4451_;
}
else
{
lean_object* v_val_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4465_; 
v_val_4457_ = lean_ctor_get(v_v_4448_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_v_4448_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4459_ = v_v_4448_;
v_isShared_4460_ = v_isSharedCheck_4465_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_val_4457_);
lean_dec(v_v_4448_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4465_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4461_; lean_object* v___x_4463_; 
lean_inc(v_fvarId_4442_);
v___x_4461_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4442_, v_e_4443_, v_val_4457_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4461_);
v___x_4463_ = v___x_4459_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
v___y_4452_ = v___x_4463_;
goto v___jp_4451_;
}
}
}
v___jp_4451_:
{
size_t v___x_4453_; size_t v___x_4454_; lean_object* v___x_4455_; 
v___x_4453_ = ((size_t)1ULL);
v___x_4454_ = lean_usize_add(v_i_4445_, v___x_4453_);
v___x_4455_ = lean_array_uset(v_bs_x27_4450_, v_i_4445_, v___y_4452_);
v_i_4445_ = v___x_4454_;
v_bs_4446_ = v___x_4455_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4466_, lean_object* v_e_4467_, lean_object* v_sz_4468_, lean_object* v_i_4469_, lean_object* v_bs_4470_){
_start:
{
size_t v_sz_boxed_4471_; size_t v_i_boxed_4472_; lean_object* v_res_4473_; 
v_sz_boxed_4471_ = lean_unbox_usize(v_sz_4468_);
lean_dec(v_sz_4468_);
v_i_boxed_4472_ = lean_unbox_usize(v_i_4469_);
lean_dec(v_i_4469_);
v_res_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4466_, v_e_4467_, v_sz_boxed_4471_, v_i_boxed_4472_, v_bs_4470_);
lean_dec_ref(v_e_4467_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4474_, lean_object* v_e_4475_, size_t v_sz_4476_, size_t v_i_4477_, lean_object* v_bs_4478_){
_start:
{
uint8_t v___x_4479_; 
v___x_4479_ = lean_usize_dec_lt(v_i_4477_, v_sz_4476_);
if (v___x_4479_ == 0)
{
lean_dec(v_fvarId_4474_);
return v_bs_4478_;
}
else
{
lean_object* v_v_4480_; lean_object* v___x_4481_; lean_object* v_bs_x27_4482_; lean_object* v___x_4483_; size_t v___x_4484_; size_t v___x_4485_; lean_object* v___x_4486_; 
v_v_4480_ = lean_array_uget(v_bs_4478_, v_i_4477_);
v___x_4481_ = lean_unsigned_to_nat(0u);
v_bs_x27_4482_ = lean_array_uset(v_bs_4478_, v_i_4477_, v___x_4481_);
lean_inc(v_fvarId_4474_);
v___x_4483_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4474_, v_e_4475_, v_v_4480_);
v___x_4484_ = ((size_t)1ULL);
v___x_4485_ = lean_usize_add(v_i_4477_, v___x_4484_);
v___x_4486_ = lean_array_uset(v_bs_x27_4482_, v_i_4477_, v___x_4483_);
v_i_4477_ = v___x_4485_;
v_bs_4478_ = v___x_4486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4488_, lean_object* v_e_4489_, lean_object* v_x_4490_){
_start:
{
if (lean_obj_tag(v_x_4490_) == 0)
{
lean_object* v_cs_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4501_; 
v_cs_4491_ = lean_ctor_get(v_x_4490_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4490_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4493_ = v_x_4490_;
v_isShared_4494_ = v_isSharedCheck_4501_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_cs_4491_);
lean_dec(v_x_4490_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4501_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
size_t v_sz_4495_; size_t v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
v_sz_4495_ = lean_array_size(v_cs_4491_);
v___x_4496_ = ((size_t)0ULL);
v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4488_, v_e_4489_, v_sz_4495_, v___x_4496_, v_cs_4491_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4497_);
v___x_4499_ = v___x_4493_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4497_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
else
{
lean_object* v_vs_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4512_; 
v_vs_4502_ = lean_ctor_get(v_x_4490_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_x_4490_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4504_ = v_x_4490_;
v_isShared_4505_ = v_isSharedCheck_4512_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_vs_4502_);
lean_dec(v_x_4490_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4512_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
size_t v_sz_4506_; size_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v_sz_4506_ = lean_array_size(v_vs_4502_);
v___x_4507_ = ((size_t)0ULL);
v___x_4508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4488_, v_e_4489_, v_sz_4506_, v___x_4507_, v_vs_4502_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4508_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4513_, lean_object* v_e_4514_, lean_object* v_x_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4513_, v_e_4514_, v_x_4515_);
lean_dec_ref(v_e_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4517_, lean_object* v_e_4518_, lean_object* v_sz_4519_, lean_object* v_i_4520_, lean_object* v_bs_4521_){
_start:
{
size_t v_sz_boxed_4522_; size_t v_i_boxed_4523_; lean_object* v_res_4524_; 
v_sz_boxed_4522_ = lean_unbox_usize(v_sz_4519_);
lean_dec(v_sz_4519_);
v_i_boxed_4523_ = lean_unbox_usize(v_i_4520_);
lean_dec(v_i_4520_);
v_res_4524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4517_, v_e_4518_, v_sz_boxed_4522_, v_i_boxed_4523_, v_bs_4521_);
lean_dec_ref(v_e_4518_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4525_, lean_object* v_e_4526_, lean_object* v_t_4527_){
_start:
{
lean_object* v_root_4528_; lean_object* v_tail_4529_; lean_object* v_size_4530_; size_t v_shift_4531_; lean_object* v_tailOff_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4543_; 
v_root_4528_ = lean_ctor_get(v_t_4527_, 0);
v_tail_4529_ = lean_ctor_get(v_t_4527_, 1);
v_size_4530_ = lean_ctor_get(v_t_4527_, 2);
v_shift_4531_ = lean_ctor_get_usize(v_t_4527_, 4);
v_tailOff_4532_ = lean_ctor_get(v_t_4527_, 3);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_t_4527_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4534_ = v_t_4527_;
v_isShared_4535_ = v_isSharedCheck_4543_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_tailOff_4532_);
lean_inc(v_size_4530_);
lean_inc(v_tail_4529_);
lean_inc(v_root_4528_);
lean_dec(v_t_4527_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4543_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; size_t v_sz_4537_; size_t v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
lean_inc(v_fvarId_4525_);
v___x_4536_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4525_, v_e_4526_, v_root_4528_);
v_sz_4537_ = lean_array_size(v_tail_4529_);
v___x_4538_ = ((size_t)0ULL);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4525_, v_e_4526_, v_sz_4537_, v___x_4538_, v_tail_4529_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 1, v___x_4539_);
lean_ctor_set(v___x_4534_, 0, v___x_4536_);
v___x_4541_ = v___x_4534_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v___x_4539_);
lean_ctor_set(v_reuseFailAlloc_4542_, 2, v_size_4530_);
lean_ctor_set(v_reuseFailAlloc_4542_, 3, v_tailOff_4532_);
lean_ctor_set_usize(v_reuseFailAlloc_4542_, 4, v_shift_4531_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4544_, lean_object* v_e_4545_, lean_object* v_t_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4544_, v_e_4545_, v_t_4546_);
lean_dec_ref(v_e_4545_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4548_, lean_object* v_x_4549_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = lean_apply_1(v_f_4548_, v_x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4551_, lean_object* v_as_4552_, lean_object* v_i_4553_, lean_object* v_acc_4554_){
_start:
{
lean_object* v___x_4555_; uint8_t v___x_4556_; 
v___x_4555_ = lean_array_get_size(v_as_4552_);
v___x_4556_ = lean_nat_dec_eq(v_i_4553_, v___x_4555_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4557_ = lean_array_fget_borrowed(v_as_4552_, v_i_4553_);
lean_inc(v_f_4551_);
lean_inc(v___x_4557_);
v___x_4558_ = lean_apply_1(v_f_4551_, v___x_4557_);
v___x_4559_ = lean_unsigned_to_nat(1u);
v___x_4560_ = lean_nat_add(v_i_4553_, v___x_4559_);
lean_dec(v_i_4553_);
v___x_4561_ = lean_array_push(v_acc_4554_, v___x_4558_);
v_i_4553_ = v___x_4560_;
v_acc_4554_ = v___x_4561_;
goto _start;
}
else
{
lean_dec(v_i_4553_);
lean_dec(v_f_4551_);
return v_acc_4554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4563_, lean_object* v_as_4564_, lean_object* v_i_4565_, lean_object* v_acc_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4563_, v_as_4564_, v_i_4565_, v_acc_4566_);
lean_dec_ref(v_as_4564_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4568_, lean_object* v_as_4569_){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = lean_array_get_size(v_as_4569_);
v___x_4572_ = lean_mk_empty_array_with_capacity(v___x_4571_);
v___x_4573_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4568_, v_as_4569_, v___x_4570_, v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4574_, lean_object* v_as_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4574_, v_as_4575_);
lean_dec_ref(v_as_4575_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4577_, size_t v_sz_4578_, size_t v_i_4579_, lean_object* v_bs_4580_){
_start:
{
uint8_t v___x_4581_; 
v___x_4581_ = lean_usize_dec_lt(v_i_4579_, v_sz_4578_);
if (v___x_4581_ == 0)
{
lean_dec(v_f_4577_);
return v_bs_4580_;
}
else
{
lean_object* v_v_4582_; lean_object* v___x_4583_; lean_object* v_bs_x27_4584_; lean_object* v___y_4586_; 
v_v_4582_ = lean_array_uget(v_bs_4580_, v_i_4579_);
v___x_4583_ = lean_unsigned_to_nat(0u);
v_bs_x27_4584_ = lean_array_uset(v_bs_4580_, v_i_4579_, v___x_4583_);
switch(lean_obj_tag(v_v_4582_))
{
case 0:
{
lean_object* v_key_4591_; lean_object* v_val_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4600_; 
v_key_4591_ = lean_ctor_get(v_v_4582_, 0);
v_val_4592_ = lean_ctor_get(v_v_4582_, 1);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_v_4582_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4594_ = v_v_4582_;
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_val_4592_);
lean_inc(v_key_4591_);
lean_dec(v_v_4582_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_inc(v_f_4577_);
v___x_4596_ = lean_apply_1(v_f_4577_, v_val_4592_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4596_);
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_key_4591_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
v___y_4586_ = v___x_4598_;
goto v___jp_4585_;
}
}
}
case 1:
{
lean_object* v_node_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4609_; 
v_node_4601_ = lean_ctor_get(v_v_4582_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_v_4582_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4603_ = v_v_4582_;
v_isShared_4604_ = v_isSharedCheck_4609_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_node_4601_);
lean_dec(v_v_4582_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4609_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
lean_inc(v_f_4577_);
v___x_4605_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4577_, v_node_4601_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 0, v___x_4605_);
v___x_4607_ = v___x_4603_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
v___y_4586_ = v___x_4607_;
goto v___jp_4585_;
}
}
}
default: 
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_box(2);
v___y_4586_ = v___x_4610_;
goto v___jp_4585_;
}
}
v___jp_4585_:
{
size_t v___x_4587_; size_t v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = ((size_t)1ULL);
v___x_4588_ = lean_usize_add(v_i_4579_, v___x_4587_);
v___x_4589_ = lean_array_uset(v_bs_x27_4584_, v_i_4579_, v___y_4586_);
v_i_4579_ = v___x_4588_;
v_bs_4580_ = v___x_4589_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4611_, lean_object* v_n_4612_){
_start:
{
if (lean_obj_tag(v_n_4612_) == 0)
{
lean_object* v_es_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4623_; 
v_es_4613_ = lean_ctor_get(v_n_4612_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v_n_4612_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4615_ = v_n_4612_;
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_es_4613_);
lean_dec(v_n_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
size_t v_sz_4617_; size_t v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v_sz_4617_ = lean_array_size(v_es_4613_);
v___x_4618_ = ((size_t)0ULL);
v___x_4619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4611_, v_sz_4617_, v___x_4618_, v_es_4613_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4619_);
v___x_4621_ = v___x_4615_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
else
{
lean_object* v_ks_4624_; lean_object* v_vs_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4633_; 
v_ks_4624_ = lean_ctor_get(v_n_4612_, 0);
v_vs_4625_ = lean_ctor_get(v_n_4612_, 1);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_n_4612_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4627_ = v_n_4612_;
v_isShared_4628_ = v_isSharedCheck_4633_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_vs_4625_);
lean_inc(v_ks_4624_);
lean_dec(v_n_4612_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4633_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v_val_4629_; lean_object* v___x_4631_; 
v_val_4629_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4611_, v_vs_4625_);
lean_dec_ref(v_vs_4625_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 1, v_val_4629_);
v___x_4631_ = v___x_4627_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_ks_4624_);
lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_val_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4634_, lean_object* v_sz_4635_, lean_object* v_i_4636_, lean_object* v_bs_4637_){
_start:
{
size_t v_sz_boxed_4638_; size_t v_i_boxed_4639_; lean_object* v_res_4640_; 
v_sz_boxed_4638_ = lean_unbox_usize(v_sz_4635_);
lean_dec(v_sz_4635_);
v_i_boxed_4639_ = lean_unbox_usize(v_i_4636_);
lean_dec(v_i_4636_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4634_, v_sz_boxed_4638_, v_i_boxed_4639_, v_bs_4637_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4641_, lean_object* v_f_4642_){
_start:
{
lean_object* v___f_4643_; lean_object* v___x_4644_; 
v___f_4643_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4643_, 0, v_f_4642_);
v___x_4644_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4643_, v_pm_4641_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4645_, lean_object* v_e_4646_, lean_object* v_lctx_4647_){
_start:
{
lean_object* v_lctx_4648_; lean_object* v_fvarIdToDecl_4649_; lean_object* v_decls_4650_; lean_object* v_auxDeclToFullName_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4661_; 
v_lctx_4648_ = l_Lean_LocalContext_erase(v_lctx_4647_, v_fvarId_4645_);
v_fvarIdToDecl_4649_ = lean_ctor_get(v_lctx_4648_, 0);
v_decls_4650_ = lean_ctor_get(v_lctx_4648_, 1);
v_auxDeclToFullName_4651_ = lean_ctor_get(v_lctx_4648_, 2);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_lctx_4648_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4653_ = v_lctx_4648_;
v_isShared_4654_ = v_isSharedCheck_4661_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_auxDeclToFullName_4651_);
lean_inc(v_decls_4650_);
lean_inc(v_fvarIdToDecl_4649_);
lean_dec(v_lctx_4648_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4661_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___f_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
lean_inc_ref(v_e_4646_);
lean_inc(v_fvarId_4645_);
v___f_4655_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4655_, 0, v_fvarId_4645_);
lean_closure_set(v___f_4655_, 1, v_e_4646_);
v___x_4656_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4649_, v___f_4655_);
v___x_4657_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4645_, v_e_4646_, v_decls_4650_);
lean_dec_ref(v_e_4646_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 1, v___x_4657_);
lean_ctor_set(v___x_4653_, 0, v___x_4656_);
v___x_4659_ = v___x_4653_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_auxDeclToFullName_4651_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4662_, lean_object* v_00_u03c3_4663_, lean_object* v_pm_4664_, lean_object* v_f_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4664_, v_f_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4667_, lean_object* v_f_4668_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4668_, v_pm_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4670_, lean_object* v_00_u03c3_4671_, lean_object* v_pm_4672_, lean_object* v_f_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4673_, v_pm_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4675_, lean_object* v_00_u03b2_4676_, lean_object* v_00_u03c3_4677_, lean_object* v_f_4678_, lean_object* v_n_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4678_, v_n_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4681_, lean_object* v_00_u03b2_4682_, lean_object* v_00_u03c3_4683_, lean_object* v_f_4684_, size_t v_sz_4685_, size_t v_i_4686_, lean_object* v_bs_4687_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4684_, v_sz_4685_, v_i_4686_, v_bs_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4689_, lean_object* v_00_u03b2_4690_, lean_object* v_00_u03c3_4691_, lean_object* v_f_4692_, lean_object* v_sz_4693_, lean_object* v_i_4694_, lean_object* v_bs_4695_){
_start:
{
size_t v_sz_boxed_4696_; size_t v_i_boxed_4697_; lean_object* v_res_4698_; 
v_sz_boxed_4696_ = lean_unbox_usize(v_sz_4693_);
lean_dec(v_sz_4693_);
v_i_boxed_4697_ = lean_unbox_usize(v_i_4694_);
lean_dec(v_i_4694_);
v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4689_, v_00_u03b2_4690_, v_00_u03c3_4691_, v_f_4692_, v_sz_boxed_4696_, v_i_boxed_4697_, v_bs_4695_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4699_, lean_object* v_00_u03b2_4700_, lean_object* v_f_4701_, lean_object* v_as_4702_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4701_, v_as_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4704_, lean_object* v_00_u03b2_4705_, lean_object* v_f_4706_, lean_object* v_as_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4704_, v_00_u03b2_4705_, v_f_4706_, v_as_4707_);
lean_dec_ref(v_as_4707_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4709_, lean_object* v_00_u03b2_4710_, lean_object* v_f_4711_, lean_object* v_as_4712_, lean_object* v_i_4713_, lean_object* v_acc_4714_, lean_object* v_hle_4715_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4711_, v_as_4712_, v_i_4713_, v_acc_4714_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4717_, lean_object* v_00_u03b2_4718_, lean_object* v_f_4719_, lean_object* v_as_4720_, lean_object* v_i_4721_, lean_object* v_acc_4722_, lean_object* v_hle_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4717_, v_00_u03b2_4718_, v_f_4719_, v_as_4720_, v_i_4721_, v_acc_4722_, v_hle_4723_);
lean_dec_ref(v_as_4720_);
return v_res_4724_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalDeclKind_default = _init_l_Lean_instInhabitedLocalDeclKind_default();
l_Lean_instInhabitedLocalDeclKind = _init_l_Lean_instInhabitedLocalDeclKind();
l_Lean_instInhabitedLocalDecl_default = _init_l_Lean_instInhabitedLocalDecl_default();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl_default);
l_Lean_instInhabitedLocalDecl = _init_l_Lean_instInhabitedLocalDecl();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl);
l_Lean_instInhabitedLocalContext_default = _init_l_Lean_instInhabitedLocalContext_default();
lean_mark_persistent(l_Lean_instInhabitedLocalContext_default);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LocalContext(builtin);
}
#ifdef __cplusplus
}
#endif
