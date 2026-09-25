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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(1u);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_LocalDecl_ctorIdx(v_x_153_);
lean_dec_ref(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
if (lean_obj_tag(v_t_155_) == 0)
{
lean_object* v_index_157_; lean_object* v_fvarId_158_; lean_object* v_userName_159_; lean_object* v_type_160_; uint8_t v_bi_161_; uint8_t v_kind_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_index_157_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_157_);
v_fvarId_158_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_158_);
v_userName_159_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_159_);
v_type_160_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_160_);
v_bi_161_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4);
v_kind_162_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_155_, 4);
v___x_163_ = lean_box(v_bi_161_);
v___x_164_ = lean_box(v_kind_162_);
v___x_165_ = lean_apply_6(v_k_156_, v_index_157_, v_fvarId_158_, v_userName_159_, v_type_160_, v___x_163_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_index_166_; lean_object* v_fvarId_167_; lean_object* v_userName_168_; lean_object* v_type_169_; lean_object* v_value_170_; uint8_t v_nondep_171_; uint8_t v_kind_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_index_166_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_166_);
v_fvarId_167_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_167_);
v_userName_168_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_168_);
v_type_169_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_169_);
v_value_170_ = lean_ctor_get(v_t_155_, 4);
lean_inc_ref(v_value_170_);
v_nondep_171_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5);
v_kind_172_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_155_, 5);
v___x_173_ = lean_box(v_nondep_171_);
v___x_174_ = lean_box(v_kind_172_);
v___x_175_ = lean_apply_7(v_k_156_, v_index_166_, v_fvarId_167_, v_userName_168_, v_type_169_, v_value_170_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_178_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_LocalDecl_ctorElim(v_motive_182_, v_ctorIdx_183_, v_t_184_, v_h_185_, v_k_186_);
lean_dec(v_ctorIdx_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_188_, lean_object* v_cdecl_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_188_, v_cdecl_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_192_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_196_, lean_object* v_ldecl_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_196_, v_ldecl_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_200_, v_ldecl_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_209_ = l_Lean_Expr_const___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = 0;
v___x_211_ = 0;
v___x_212_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_213_ = lean_box(0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4, v___x_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4 + 1, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_218_, lean_object* v_fvarId_219_, lean_object* v_userName_220_, lean_object* v_type_221_, uint8_t v_bi_222_){
_start:
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_224_, 0, v_index_218_);
lean_ctor_set(v___x_224_, 1, v_fvarId_219_);
lean_ctor_set(v___x_224_, 2, v_userName_220_);
lean_ctor_set(v___x_224_, 3, v_type_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4, v_bi_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4 + 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, lean_object* v_bi_229_){
_start:
{
uint8_t v_bi_boxed_230_; lean_object* v_res_231_; 
v_bi_boxed_230_ = lean_unbox(v_bi_229_);
v_res_231_ = lean_mk_local_decl(v_index_225_, v_fvarId_226_, v_userName_227_, v_type_228_, v_bi_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_val_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = 0;
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_239_, 0, v_index_232_);
lean_ctor_set(v___x_239_, 1, v_fvarId_233_);
lean_ctor_set(v___x_239_, 2, v_userName_234_);
lean_ctor_set(v___x_239_, 3, v_type_235_);
lean_ctor_set(v___x_239_, 4, v_val_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5 + 1, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
uint8_t v_bi_241_; 
v_bi_241_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*4);
lean_dec_ref_known(v_x_240_, 4);
return v_bi_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref(v_x_240_);
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = lean_local_decl_binder_info(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_246_, uint8_t v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
uint8_t v_nondep_249_; 
v_nondep_249_ = lean_ctor_get_uint8(v_x_246_, sizeof(void*)*5);
if (v_nondep_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
return v_x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_x_53__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_53__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_LocalDecl_isLet(v_x_251_, v_x_53__boxed_253_);
lean_dec_ref(v_x_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_256_){
_start:
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_index_257_);
return v_index_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_LocalDecl_index(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_fvarId_262_; lean_object* v_userName_263_; lean_object* v_type_264_; uint8_t v_bi_265_; uint8_t v_kind_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_fvarId_262_ = lean_ctor_get(v_x_260_, 1);
v_userName_263_ = lean_ctor_get(v_x_260_, 2);
v_type_264_ = lean_ctor_get(v_x_260_, 3);
v_bi_265_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4);
v_kind_266_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4 + 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_274_);
v___x_268_ = v_x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_type_264_);
lean_inc(v_userName_263_);
lean_inc(v_fvarId_262_);
lean_dec(v_x_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_x_261_);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_fvarId_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_userName_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_type_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4, v_bi_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4 + 1, v_kind_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_fvarId_275_; lean_object* v_userName_276_; lean_object* v_type_277_; lean_object* v_value_278_; uint8_t v_nondep_279_; uint8_t v_kind_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_fvarId_275_ = lean_ctor_get(v_x_260_, 1);
v_userName_276_ = lean_ctor_get(v_x_260_, 2);
v_type_277_ = lean_ctor_get(v_x_260_, 3);
v_value_278_ = lean_ctor_get(v_x_260_, 4);
v_nondep_279_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5);
v_kind_280_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5 + 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_288_);
v___x_282_ = v_x_260_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_value_278_);
lean_inc(v_type_277_);
lean_inc(v_userName_276_);
lean_inc(v_fvarId_275_);
lean_dec(v_x_260_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_x_261_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_fvarId_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_userName_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_type_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_value_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5, v_nondep_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5 + 1, v_kind_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_289_){
_start:
{
lean_object* v_fvarId_290_; 
v_fvarId_290_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_fvarId_290_);
return v_fvarId_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_LocalDecl_fvarId(v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_293_){
_start:
{
lean_object* v_userName_294_; 
v_userName_294_ = lean_ctor_get(v_x_293_, 2);
lean_inc(v_userName_294_);
return v_userName_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_LocalDecl_userName(v_x_295_);
lean_dec_ref(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_297_){
_start:
{
lean_object* v_type_298_; 
v_type_298_ = lean_ctor_get(v_x_297_, 3);
lean_inc_ref(v_type_298_);
return v_type_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_LocalDecl_type(v_x_299_);
lean_dec_ref(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_index_303_; lean_object* v_fvarId_304_; lean_object* v_userName_305_; uint8_t v_bi_306_; uint8_t v_kind_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_index_303_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_304_ = lean_ctor_get(v_x_301_, 1);
v_userName_305_ = lean_ctor_get(v_x_301_, 2);
v_bi_306_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4);
v_kind_307_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4 + 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_315_);
v___x_309_ = v_x_301_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_userName_305_);
lean_inc(v_fvarId_304_);
lean_inc(v_index_303_);
lean_dec(v_x_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v_x_302_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_index_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_fvarId_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_userName_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_x_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4, v_bi_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4 + 1, v_kind_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_index_316_; lean_object* v_fvarId_317_; lean_object* v_userName_318_; lean_object* v_value_319_; uint8_t v_nondep_320_; uint8_t v_kind_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_index_316_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_317_ = lean_ctor_get(v_x_301_, 1);
v_userName_318_ = lean_ctor_get(v_x_301_, 2);
v_value_319_ = lean_ctor_get(v_x_301_, 4);
v_nondep_320_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5);
v_kind_321_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5 + 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_329_);
v___x_323_ = v_x_301_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_value_319_);
lean_inc(v_userName_318_);
lean_inc(v_fvarId_317_);
lean_inc(v_index_316_);
lean_dec(v_x_301_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v_x_302_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_index_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fvarId_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_userName_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_value_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5, v_nondep_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5 + 1, v_kind_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v_bi_331_; 
v_bi_331_ = lean_ctor_get_uint8(v_x_330_, sizeof(void*)*4);
return v_bi_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_LocalDecl_binderInfo(v_x_333_);
lean_dec_ref(v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
uint8_t v_kind_337_; 
v_kind_337_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*4 + 1);
return v_kind_337_;
}
else
{
uint8_t v_kind_338_; 
v_kind_338_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*5 + 1);
return v_kind_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_LocalDecl_kind(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isAuxDecl___closed__0(void){
_start:
{
uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_342_ = 2;
v___x_343_ = l_Lean_LocalDeclKind_ctorIdx(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_344_){
_start:
{
uint8_t v___y_346_; 
if (lean_obj_tag(v_d_344_) == 0)
{
uint8_t v_kind_350_; 
v_kind_350_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*4 + 1);
v___y_346_ = v_kind_350_;
goto v___jp_345_;
}
else
{
uint8_t v_kind_351_; 
v_kind_351_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*5 + 1);
v___y_346_ = v_kind_351_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_LocalDeclKind_ctorIdx(v___y_346_);
v___x_348_ = lean_obj_once(&l_Lean_LocalDecl_isAuxDecl___closed__0, &l_Lean_LocalDecl_isAuxDecl___closed__0_once, _init_l_Lean_LocalDecl_isAuxDecl___closed__0);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_LocalDecl_isAuxDecl(v_d_352_);
lean_dec_ref(v_d_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isImplementationDetail___closed__0(void){
_start:
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_LocalDeclKind_ctorIdx(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_366_; 
v_kind_366_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_366_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = l_Lean_LocalDeclKind_ctorIdx(v___y_359_);
v___x_361_ = lean_obj_once(&l_Lean_LocalDecl_isImplementationDetail___closed__0, &l_Lean_LocalDecl_isImplementationDetail___closed__0_once, _init_l_Lean_LocalDecl_isImplementationDetail___closed__0);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 1;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_LocalDecl_isImplementationDetail(v_d_367_);
lean_dec_ref(v_d_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_370_, uint8_t v_x_371_){
_start:
{
if (lean_obj_tag(v_x_370_) == 1)
{
uint8_t v_nondep_372_; 
v_nondep_372_ = lean_ctor_get_uint8(v_x_370_, sizeof(void*)*5);
if (v_nondep_372_ == 0)
{
lean_object* v_value_373_; lean_object* v___x_374_; 
v_value_373_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_373_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_value_373_);
return v___x_374_;
}
else
{
if (v_x_371_ == 1)
{
lean_object* v_value_375_; lean_object* v___x_376_; 
v_value_375_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_375_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_value_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_x_47__boxed_381_; lean_object* v_res_382_; 
v_x_47__boxed_381_ = lean_unbox(v_x_380_);
v_res_382_ = l_Lean_LocalDecl_value_x3f(v_x_379_, v_x_47__boxed_381_);
lean_dec_ref(v_x_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_instInhabitedExpr;
v___x_385_ = lean_panic_fn_borrowed(v___x_384_, v_msg_383_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_390_ = lean_unsigned_to_nat(54u);
v___x_391_ = lean_unsigned_to_nat(172u);
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_393_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_394_ = l_mkPanicMessageWithDecl(v___x_393_, v___x_392_, v___x_391_, v___x_390_, v___x_389_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_397_ = lean_unsigned_to_nat(54u);
v___x_398_ = lean_unsigned_to_nat(175u);
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_400_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_402_, uint8_t v_x_403_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_405_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_404_);
return v___x_405_;
}
else
{
uint8_t v_nondep_406_; 
v_nondep_406_ = lean_ctor_get_uint8(v_x_402_, sizeof(void*)*5);
if (v_nondep_406_ == 0)
{
lean_object* v_value_407_; 
v_value_407_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_407_);
return v_value_407_;
}
else
{
if (v_x_403_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_409_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_value_410_; 
v_value_410_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_410_);
return v_value_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v_x_143__boxed_413_; lean_object* v_res_414_; 
v_x_143__boxed_413_ = lean_unbox(v_x_412_);
v_res_414_ = l_Lean_LocalDecl_value(v_x_411_, v_x_143__boxed_413_);
lean_dec_ref(v_x_411_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_415_, uint8_t v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
uint8_t v_nondep_418_; 
v_nondep_418_ = lean_ctor_get_uint8(v_x_415_, sizeof(void*)*5);
if (v_nondep_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = 1;
return v___x_419_;
}
else
{
return v_x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_x_72__boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_x_72__boxed_422_ = lean_unbox(v_x_421_);
v_res_423_ = l_Lean_LocalDecl_hasValue(v_x_420_, v_x_72__boxed_422_);
lean_dec_ref(v_x_420_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_425_) == 1)
{
lean_object* v_index_427_; lean_object* v_fvarId_428_; lean_object* v_userName_429_; lean_object* v_type_430_; uint8_t v_nondep_431_; uint8_t v_kind_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_index_427_ = lean_ctor_get(v_x_425_, 0);
v_fvarId_428_ = lean_ctor_get(v_x_425_, 1);
v_userName_429_ = lean_ctor_get(v_x_425_, 2);
v_type_430_ = lean_ctor_get(v_x_425_, 3);
v_nondep_431_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5);
v_kind_432_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5 + 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v_x_425_, 4);
lean_dec(v_unused_440_);
v___x_434_ = v_x_425_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_type_430_);
lean_inc(v_userName_429_);
lean_inc(v_fvarId_428_);
lean_inc(v_index_427_);
lean_dec(v_x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v_x_426_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_index_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_fvarId_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_userName_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_type_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_x_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5, v_nondep_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5 + 1, v_kind_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_dec_ref(v_x_426_);
return v_x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_441_, uint8_t v_x_442_){
_start:
{
if (lean_obj_tag(v_x_441_) == 1)
{
lean_object* v_index_443_; lean_object* v_fvarId_444_; lean_object* v_userName_445_; lean_object* v_type_446_; lean_object* v_value_447_; uint8_t v_kind_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_index_443_ = lean_ctor_get(v_x_441_, 0);
v_fvarId_444_ = lean_ctor_get(v_x_441_, 1);
v_userName_445_ = lean_ctor_get(v_x_441_, 2);
v_type_446_ = lean_ctor_get(v_x_441_, 3);
v_value_447_ = lean_ctor_get(v_x_441_, 4);
v_kind_448_ = lean_ctor_get_uint8(v_x_441_, sizeof(void*)*5 + 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_x_441_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_value_447_);
lean_inc(v_type_446_);
lean_inc(v_userName_445_);
lean_inc(v_fvarId_444_);
lean_inc(v_index_443_);
lean_dec(v_x_441_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_index_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_fvarId_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_userName_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_type_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_value_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*5 + 1, v_kind_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*5, v_x_442_);
return v___x_453_;
}
}
}
else
{
return v_x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_x_23__boxed_458_; lean_object* v_res_459_; 
v_x_23__boxed_458_ = lean_unbox(v_x_457_);
v_res_459_ = l_Lean_LocalDecl_setNondep(v_x_456_, v_x_23__boxed_458_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 1)
{
uint8_t v_nondep_461_; 
v_nondep_461_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*5);
return v_nondep_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_LocalDecl_isNondep(v_x_463_);
lean_dec_ref(v_x_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_index_468_; lean_object* v_fvarId_469_; lean_object* v_type_470_; uint8_t v_bi_471_; uint8_t v_kind_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_index_468_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_469_ = lean_ctor_get(v_x_466_, 1);
v_type_470_ = lean_ctor_get(v_x_466_, 3);
v_bi_471_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4);
v_kind_472_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4 + 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_480_);
v___x_474_ = v_x_466_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_type_470_);
lean_inc(v_fvarId_469_);
lean_inc(v_index_468_);
lean_dec(v_x_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 2, v_x_467_);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_index_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_fvarId_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_type_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4, v_bi_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4 + 1, v_kind_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_index_481_; lean_object* v_fvarId_482_; lean_object* v_type_483_; lean_object* v_value_484_; uint8_t v_nondep_485_; uint8_t v_kind_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_index_481_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_482_ = lean_ctor_get(v_x_466_, 1);
v_type_483_ = lean_ctor_get(v_x_466_, 3);
v_value_484_ = lean_ctor_get(v_x_466_, 4);
v_nondep_485_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5);
v_kind_486_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5 + 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_494_);
v___x_488_ = v_x_466_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_value_484_);
lean_inc(v_type_483_);
lean_inc(v_fvarId_482_);
lean_inc(v_index_481_);
lean_dec(v_x_466_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v_x_467_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_index_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_fvarId_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_type_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_value_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5, v_nondep_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5 + 1, v_kind_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lean_instInhabitedLocalDecl_default;
v___x_497_ = lean_panic_fn_borrowed(v___x_496_, v_msg_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_501_ = lean_unsigned_to_nat(38u);
v___x_502_ = lean_unsigned_to_nat(237u);
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_504_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_505_ = l_mkPanicMessageWithDecl(v___x_504_, v___x_503_, v___x_502_, v___x_501_, v___x_500_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_506_, uint8_t v_x_507_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_index_508_; lean_object* v_fvarId_509_; lean_object* v_userName_510_; lean_object* v_type_511_; uint8_t v_kind_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_index_508_ = lean_ctor_get(v_x_506_, 0);
v_fvarId_509_ = lean_ctor_get(v_x_506_, 1);
v_userName_510_ = lean_ctor_get(v_x_506_, 2);
v_type_511_ = lean_ctor_get(v_x_506_, 3);
v_kind_512_ = lean_ctor_get_uint8(v_x_506_, sizeof(void*)*4 + 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v_x_506_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_type_511_);
lean_inc(v_userName_510_);
lean_inc(v_fvarId_509_);
lean_inc(v_index_508_);
lean_dec(v_x_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_index_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_fvarId_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_userName_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_type_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_518_, sizeof(void*)*4 + 1, v_kind_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*4, v_x_507_);
return v___x_517_;
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref_known(v_x_506_, 5);
v___x_520_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_521_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_x_84__boxed_524_; lean_object* v_res_525_; 
v_x_84__boxed_524_ = lean_unbox(v_x_523_);
v_res_525_ = l_Lean_LocalDecl_setBinderInfo(v_x_522_, v_x_84__boxed_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_526_){
_start:
{
lean_object* v_fvarId_527_; lean_object* v___x_528_; 
v_fvarId_527_ = lean_ctor_get(v_decl_526_, 1);
lean_inc(v_fvarId_527_);
lean_dec_ref(v_decl_526_);
v___x_528_ = l_Lean_mkFVar(v_fvarId_527_);
return v___x_528_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_type_530_; uint8_t v___x_531_; 
v_type_530_ = lean_ctor_get(v_x_529_, 3);
v___x_531_ = l_Lean_Expr_hasExprMVar(v_type_530_);
return v___x_531_;
}
else
{
lean_object* v_type_532_; lean_object* v_value_533_; uint8_t v___x_534_; 
v_type_532_ = lean_ctor_get(v_x_529_, 3);
v_value_533_ = lean_ctor_get(v_x_529_, 4);
v___x_534_ = l_Lean_Expr_hasExprMVar(v_type_532_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_Expr_hasExprMVar(v_value_533_);
return v___x_535_;
}
else
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_LocalDecl_hasExprMVar(v_x_536_);
lean_dec_ref(v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_539_, uint8_t v_x_540_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_index_541_; lean_object* v_fvarId_542_; lean_object* v_userName_543_; lean_object* v_type_544_; uint8_t v_bi_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_index_541_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_542_ = lean_ctor_get(v_x_539_, 1);
v_userName_543_ = lean_ctor_get(v_x_539_, 2);
v_type_544_ = lean_ctor_get(v_x_539_, 3);
v_bi_545_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*4);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_539_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_type_544_);
lean_inc(v_userName_543_);
lean_inc(v_fvarId_542_);
lean_inc(v_index_541_);
lean_dec(v_x_539_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_index_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_fvarId_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_userName_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_type_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*4, v_bi_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*4 + 1, v_x_540_);
return v___x_550_;
}
}
}
else
{
lean_object* v_index_553_; lean_object* v_fvarId_554_; lean_object* v_userName_555_; lean_object* v_type_556_; lean_object* v_value_557_; uint8_t v_nondep_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_index_553_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_554_ = lean_ctor_get(v_x_539_, 1);
v_userName_555_ = lean_ctor_get(v_x_539_, 2);
v_type_556_ = lean_ctor_get(v_x_539_, 3);
v_value_557_ = lean_ctor_get(v_x_539_, 4);
v_nondep_558_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*5);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_x_539_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_value_557_);
lean_inc(v_type_556_);
lean_inc(v_userName_555_);
lean_inc(v_fvarId_554_);
lean_inc(v_index_553_);
lean_dec(v_x_539_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_index_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_fvarId_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_userName_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_type_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_value_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*5, v_nondep_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*5 + 1, v_x_540_);
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_x_31__boxed_568_; lean_object* v_res_569_; 
v_x_31__boxed_568_ = lean_unbox(v_x_567_);
v_res_569_ = l_Lean_LocalDecl_setKind(v_x_566_, v_x_31__boxed_568_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_570_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_577_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_ctor_set_usize(v___x_581_, 4, v___x_576_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(1);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_584_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_instInhabitedLocalContext_default;
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(32u);
v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
lean_dec_ref(v___x_590_);
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkEmpty___redArg___boxed(lean_object* v___dummy_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_LocalContext_mkEmpty___redArg();
return v_res_593_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_LocalContext_mkEmpty___redArg();
return v___x_594_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_LocalContext_mkEmpty___closed__0, &l_Lean_LocalContext_mkEmpty___closed__0_once, _init_l_Lean_LocalContext_mkEmpty___closed__0);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_unsigned_to_nat(32u);
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
lean_dec_ref(v___x_598_);
v___x_599_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_602_);
lean_dec_ref(v_x_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_605_, lean_object* v_x_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_608_, v_x_609_);
lean_dec_ref(v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isEmpty(lean_object* v_lctx_612_){
_start:
{
lean_object* v_fvarIdToDecl_613_; uint8_t v___x_614_; 
v_fvarIdToDecl_613_ = lean_ctor_get(v_lctx_612_, 0);
v___x_614_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_LocalContext_isEmpty(v_lctx_615_);
lean_dec_ref(v_lctx_615_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_647_; 
v_ks_622_ = lean_ctor_get(v_x_618_, 0);
v_vs_623_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_647_ == 0)
{
v___x_625_ = v_x_618_;
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_vs_623_);
lean_inc(v_ks_622_);
lean_dec(v_x_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_array_get_size(v_ks_622_);
v___x_628_ = lean_nat_dec_lt(v_x_619_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v_x_619_);
v___x_629_ = lean_array_push(v_ks_622_, v_x_620_);
v___x_630_ = lean_array_push(v_vs_623_, v_x_621_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_630_);
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v_k_x27_634_; uint8_t v___x_635_; 
v_k_x27_634_ = lean_array_fget_borrowed(v_ks_622_, v_x_619_);
v___x_635_ = l_Lean_instBEqFVarId_beq(v_x_620_, v_k_x27_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_637_; 
if (v_isShared_626_ == 0)
{
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_ks_622_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_vs_623_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_x_619_, v___x_638_);
lean_dec(v_x_619_);
v_x_618_ = v___x_637_;
v_x_619_ = v___x_639_;
goto _start;
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_array_fset(v_ks_622_, v_x_619_, v_x_620_);
v___x_643_ = lean_array_fset(v_vs_623_, v_x_619_, v_x_621_);
lean_dec(v_x_619_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_643_);
lean_ctor_set(v___x_625_, 0, v___x_642_);
v___x_645_ = v___x_625_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_648_, lean_object* v_k_649_, lean_object* v_v_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_648_, v___x_651_, v_k_649_, v_v_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_654_, size_t v_x_655_, size_t v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_659_; size_t v___x_660_; size_t v___x_661_; lean_object* v_j_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_es_659_ = lean_ctor_get(v_x_654_, 0);
v___x_660_ = ((size_t)31ULL);
v___x_661_ = lean_usize_land(v_x_655_, v___x_660_);
v_j_662_ = lean_usize_to_nat(v___x_661_);
v___x_663_ = lean_array_get_size(v_es_659_);
v___x_664_ = lean_nat_dec_lt(v_j_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec(v_j_662_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
return v_x_654_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_es_659_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_654_, 0);
lean_dec(v_unused_704_);
v___x_666_ = v_x_654_;
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_x_654_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_703_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_v_668_; lean_object* v___x_669_; lean_object* v_xs_x27_670_; lean_object* v___y_672_; 
v_v_668_ = lean_array_fget(v_es_659_, v_j_662_);
v___x_669_ = lean_box(0);
v_xs_x27_670_ = lean_array_fset(v_es_659_, v_j_662_, v___x_669_);
switch(lean_obj_tag(v_v_668_))
{
case 0:
{
lean_object* v_key_677_; lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
v_key_677_ = lean_ctor_get(v_v_668_, 0);
v_val_678_ = lean_ctor_get(v_v_668_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_v_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_680_ = v_v_668_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_inc(v_key_677_);
lean_dec(v_v_668_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_instBEqFVarId_beq(v_x_657_, v_key_677_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_del_object(v___x_680_);
v___x_683_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_677_, v_val_678_, v_x_657_, v_x_658_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
v___y_672_ = v___x_684_;
goto v___jp_671_;
}
else
{
lean_object* v___x_686_; 
lean_dec(v_val_678_);
lean_dec(v_key_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_x_658_);
lean_ctor_set(v___x_680_, 0, v_x_657_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_x_658_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v___y_672_ = v___x_686_;
goto v___jp_671_;
}
}
}
}
case 1:
{
lean_object* v_node_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_node_689_ = lean_ctor_get(v_v_668_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_v_668_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v_v_668_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_node_689_);
lean_dec(v_v_668_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_usize_shift_right(v_x_655_, v___x_693_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_x_656_, v___x_695_);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_689_, v___x_694_, v___x_696_, v_x_657_, v_x_658_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_697_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_672_ = v___x_699_;
goto v___jp_671_;
}
}
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_x_657_);
lean_ctor_set(v___x_702_, 1, v_x_658_);
v___y_672_ = v___x_702_;
goto v___jp_671_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_array_fset(v_xs_x27_670_, v_j_662_, v___y_672_);
lean_dec(v_j_662_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_673_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_ks_705_; lean_object* v_vs_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_724_; 
v_ks_705_ = lean_ctor_get(v_x_654_, 0);
v_vs_706_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_724_ == 0)
{
v___x_708_ = v_x_654_;
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_vs_706_);
lean_inc(v_ks_705_);
lean_dec(v_x_654_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_724_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_ks_705_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_vs_706_);
v___x_711_ = v_reuseFailAlloc_723_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_newNode_712_; size_t v___x_713_; uint8_t v___x_714_; 
v_newNode_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_711_, v_x_657_, v_x_658_);
v___x_713_ = ((size_t)7ULL);
v___x_714_ = lean_usize_dec_le(v___x_713_, v_x_656_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_712_);
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
if (v___x_717_ == 0)
{
lean_object* v_ks_718_; lean_object* v_vs_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_ks_718_ = lean_ctor_get(v_newNode_712_, 0);
lean_inc_ref(v_ks_718_);
v_vs_719_ = lean_ctor_get(v_newNode_712_, 1);
lean_inc_ref(v_vs_719_);
lean_dec_ref(v_newNode_712_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_656_, v_ks_718_, v_vs_719_, v___x_720_, v___x_721_);
lean_dec_ref(v_vs_719_);
lean_dec_ref(v_ks_718_);
return v___x_722_;
}
else
{
return v_newNode_712_;
}
}
else
{
return v_newNode_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_725_, lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_i_728_, lean_object* v_entries_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_keys_726_);
v___x_731_ = lean_nat_dec_lt(v_i_728_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_i_728_);
return v_entries_729_;
}
else
{
lean_object* v_k_732_; lean_object* v_v_733_; uint64_t v___x_734_; size_t v_h_735_; size_t v___x_736_; lean_object* v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v_h_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_k_732_ = lean_array_fget_borrowed(v_keys_726_, v_i_728_);
v_v_733_ = lean_array_fget_borrowed(v_vals_727_, v_i_728_);
v___x_734_ = l_Lean_instHashableFVarId_hash(v_k_732_);
v_h_735_ = lean_uint64_to_usize(v___x_734_);
v___x_736_ = ((size_t)5ULL);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_sub(v_depth_725_, v___x_738_);
v___x_740_ = lean_usize_mul(v___x_736_, v___x_739_);
v_h_741_ = lean_usize_shift_right(v_h_735_, v___x_740_);
v___x_742_ = lean_nat_add(v_i_728_, v___x_737_);
lean_dec(v_i_728_);
lean_inc(v_v_733_);
lean_inc(v_k_732_);
v___x_743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_729_, v_h_741_, v_depth_725_, v_k_732_, v_v_733_);
v_i_728_ = v___x_742_;
v_entries_729_ = v___x_743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_745_, lean_object* v_keys_746_, lean_object* v_vals_747_, lean_object* v_i_748_, lean_object* v_entries_749_){
_start:
{
size_t v_depth_boxed_750_; lean_object* v_res_751_; 
v_depth_boxed_750_ = lean_unbox_usize(v_depth_745_);
lean_dec(v_depth_745_);
v_res_751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_750_, v_keys_746_, v_vals_747_, v_i_748_, v_entries_749_);
lean_dec_ref(v_vals_747_);
lean_dec_ref(v_keys_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
size_t v_x_365__boxed_757_; size_t v_x_366__boxed_758_; lean_object* v_res_759_; 
v_x_365__boxed_757_ = lean_unbox_usize(v_x_753_);
lean_dec(v_x_753_);
v_x_366__boxed_758_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_res_759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_752_, v_x_365__boxed_757_, v_x_366__boxed_758_, v_x_755_, v_x_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint64_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_763_ = l_Lean_instHashableFVarId_hash(v_x_761_);
v___x_764_ = lean_uint64_to_usize(v___x_763_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_760_, v___x_764_, v___x_765_, v_x_761_, v_x_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_767_, lean_object* v_fvarId_768_, lean_object* v_userName_769_, lean_object* v_type_770_, uint8_t v_bi_771_, uint8_t v_kind_772_){
_start:
{
lean_object* v_decls_773_; lean_object* v_fvarIdToDecl_774_; lean_object* v_auxDeclToFullName_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_decls_773_ = lean_ctor_get(v_lctx_767_, 1);
v_fvarIdToDecl_774_ = lean_ctor_get(v_lctx_767_, 0);
v_auxDeclToFullName_775_ = lean_ctor_get(v_lctx_767_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_lctx_767_);
if (v_isSharedCheck_787_ == 0)
{
v___x_777_ = v_lctx_767_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_auxDeclToFullName_775_);
lean_inc(v_decls_773_);
lean_inc(v_fvarIdToDecl_774_);
lean_dec(v_lctx_767_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_size_779_; lean_object* v_decl_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v_size_779_ = lean_ctor_get(v_decls_773_, 2);
lean_inc(v_fvarId_768_);
lean_inc(v_size_779_);
v_decl_780_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_780_, 0, v_size_779_);
lean_ctor_set(v_decl_780_, 1, v_fvarId_768_);
lean_ctor_set(v_decl_780_, 2, v_userName_769_);
lean_ctor_set(v_decl_780_, 3, v_type_770_);
lean_ctor_set_uint8(v_decl_780_, sizeof(void*)*4, v_bi_771_);
lean_ctor_set_uint8(v_decl_780_, sizeof(void*)*4 + 1, v_kind_772_);
lean_inc_ref(v_decl_780_);
v___x_781_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_774_, v_fvarId_768_, v_decl_780_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v_decl_780_);
v___x_783_ = l_Lean_PersistentArray_push___redArg(v_decls_773_, v___x_782_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_783_);
lean_ctor_set(v___x_777_, 0, v___x_781_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_auxDeclToFullName_775_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_788_, lean_object* v_fvarId_789_, lean_object* v_userName_790_, lean_object* v_type_791_, lean_object* v_bi_792_, lean_object* v_kind_793_){
_start:
{
uint8_t v_bi_boxed_794_; uint8_t v_kind_boxed_795_; lean_object* v_res_796_; 
v_bi_boxed_794_ = lean_unbox(v_bi_792_);
v_kind_boxed_795_ = lean_unbox(v_kind_793_);
v_res_796_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_788_, v_fvarId_789_, v_userName_790_, v_type_791_, v_bi_boxed_794_, v_kind_boxed_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_803_, v_x_804_, v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_565__boxed_815_; size_t v_x_566__boxed_816_; lean_object* v_res_817_; 
v_x_565__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_566__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_809_, v_x_810_, v_x_565__boxed_815_, v_x_566__boxed_816_, v_x_813_, v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_818_, lean_object* v_n_819_, lean_object* v_k_820_, lean_object* v_v_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_819_, v_k_820_, v_v_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_823_, size_t v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_824_, v_keys_825_, v_vals_826_, v_i_828_, v_entries_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_831_, lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
size_t v_depth_boxed_838_; lean_object* v_res_839_; 
v_depth_boxed_838_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_831_, v_depth_boxed_838_, v_keys_833_, v_vals_834_, v_heq_835_, v_i_836_, v_entries_837_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_846_, lean_object* v_fvarId_847_, lean_object* v_userName_848_, lean_object* v_type_849_, uint8_t v_bi_850_){
_start:
{
uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_851_ = 0;
v___x_852_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_846_, v_fvarId_847_, v_userName_848_, v_type_849_, v_bi_850_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_853_, lean_object* v_fvarId_854_, lean_object* v_userName_855_, lean_object* v_type_856_, lean_object* v_bi_857_){
_start:
{
uint8_t v_bi_boxed_858_; lean_object* v_res_859_; 
v_bi_boxed_858_ = lean_unbox(v_bi_857_);
v_res_859_ = lean_local_ctx_mk_local_decl(v_lctx_853_, v_fvarId_854_, v_userName_855_, v_type_856_, v_bi_boxed_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_860_, lean_object* v_fvarId_861_, lean_object* v_userName_862_, lean_object* v_type_863_, lean_object* v_value_864_, uint8_t v_nondep_865_, uint8_t v_kind_866_){
_start:
{
lean_object* v_decls_867_; lean_object* v_fvarIdToDecl_868_; lean_object* v_auxDeclToFullName_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_881_; 
v_decls_867_ = lean_ctor_get(v_lctx_860_, 1);
v_fvarIdToDecl_868_ = lean_ctor_get(v_lctx_860_, 0);
v_auxDeclToFullName_869_ = lean_ctor_get(v_lctx_860_, 2);
v_isSharedCheck_881_ = !lean_is_exclusive(v_lctx_860_);
if (v_isSharedCheck_881_ == 0)
{
v___x_871_ = v_lctx_860_;
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_auxDeclToFullName_869_);
lean_inc(v_decls_867_);
lean_inc(v_fvarIdToDecl_868_);
lean_dec(v_lctx_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_size_873_; lean_object* v_decl_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v_size_873_ = lean_ctor_get(v_decls_867_, 2);
lean_inc(v_fvarId_861_);
lean_inc(v_size_873_);
v_decl_874_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_874_, 0, v_size_873_);
lean_ctor_set(v_decl_874_, 1, v_fvarId_861_);
lean_ctor_set(v_decl_874_, 2, v_userName_862_);
lean_ctor_set(v_decl_874_, 3, v_type_863_);
lean_ctor_set(v_decl_874_, 4, v_value_864_);
lean_ctor_set_uint8(v_decl_874_, sizeof(void*)*5, v_nondep_865_);
lean_ctor_set_uint8(v_decl_874_, sizeof(void*)*5 + 1, v_kind_866_);
lean_inc_ref(v_decl_874_);
v___x_875_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_868_, v_fvarId_861_, v_decl_874_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_decl_874_);
v___x_877_ = l_Lean_PersistentArray_push___redArg(v_decls_867_, v___x_876_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_877_);
lean_ctor_set(v___x_871_, 0, v___x_875_);
v___x_879_ = v___x_871_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_auxDeclToFullName_869_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_882_, lean_object* v_fvarId_883_, lean_object* v_userName_884_, lean_object* v_type_885_, lean_object* v_value_886_, lean_object* v_nondep_887_, lean_object* v_kind_888_){
_start:
{
uint8_t v_nondep_boxed_889_; uint8_t v_kind_boxed_890_; lean_object* v_res_891_; 
v_nondep_boxed_889_ = lean_unbox(v_nondep_887_);
v_kind_boxed_890_ = lean_unbox(v_kind_888_);
v_res_891_ = l_Lean_LocalContext_mkLetDecl(v_lctx_882_, v_fvarId_883_, v_userName_884_, v_type_885_, v_value_886_, v_nondep_boxed_889_, v_kind_boxed_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_892_, lean_object* v_fvarId_893_, lean_object* v_userName_894_, lean_object* v_type_895_, lean_object* v_value_896_, uint8_t v_nondep_897_){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_898_ = 0;
v___x_899_ = l_Lean_LocalContext_mkLetDecl(v_lctx_892_, v_fvarId_893_, v_userName_894_, v_type_895_, v_value_896_, v_nondep_897_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_900_, lean_object* v_fvarId_901_, lean_object* v_userName_902_, lean_object* v_type_903_, lean_object* v_value_904_, lean_object* v_nondep_905_){
_start:
{
uint8_t v_nondep_boxed_906_; lean_object* v_res_907_; 
v_nondep_boxed_906_ = lean_unbox(v_nondep_905_);
v_res_907_ = lean_local_ctx_mk_let_decl(v_lctx_900_, v_fvarId_901_, v_userName_902_, v_type_903_, v_value_904_, v_nondep_boxed_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_908_, lean_object* v_fvarId_909_, lean_object* v_userName_910_, lean_object* v_type_911_, lean_object* v_fullName_912_){
_start:
{
lean_object* v_decls_913_; lean_object* v_fvarIdToDecl_914_; lean_object* v_auxDeclToFullName_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_930_; 
v_decls_913_ = lean_ctor_get(v_lctx_908_, 1);
v_fvarIdToDecl_914_ = lean_ctor_get(v_lctx_908_, 0);
v_auxDeclToFullName_915_ = lean_ctor_get(v_lctx_908_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_lctx_908_);
if (v_isSharedCheck_930_ == 0)
{
v___x_917_ = v_lctx_908_;
v_isShared_918_ = v_isSharedCheck_930_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_auxDeclToFullName_915_);
lean_inc(v_decls_913_);
lean_inc(v_fvarIdToDecl_914_);
lean_dec(v_lctx_908_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_930_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_size_919_; uint8_t v___x_920_; uint8_t v___x_921_; lean_object* v_decl_922_; lean_object* v_auxDeclToFullName_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_size_919_ = lean_ctor_get(v_decls_913_, 2);
v___x_920_ = 0;
v___x_921_ = 2;
lean_inc_n(v_fvarId_909_, 2);
lean_inc(v_size_919_);
v_decl_922_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_922_, 0, v_size_919_);
lean_ctor_set(v_decl_922_, 1, v_fvarId_909_);
lean_ctor_set(v_decl_922_, 2, v_userName_910_);
lean_ctor_set(v_decl_922_, 3, v_type_911_);
lean_ctor_set_uint8(v_decl_922_, sizeof(void*)*4, v___x_920_);
lean_ctor_set_uint8(v_decl_922_, sizeof(void*)*4 + 1, v___x_921_);
v_auxDeclToFullName_923_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_909_, v_fullName_912_, v_auxDeclToFullName_915_);
lean_inc_ref(v_decl_922_);
v___x_924_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_914_, v_fvarId_909_, v_decl_922_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_decl_922_);
v___x_926_ = l_Lean_PersistentArray_push___redArg(v_decls_913_, v___x_925_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 2, v_auxDeclToFullName_923_);
lean_ctor_set(v___x_917_, 1, v___x_926_);
lean_ctor_set(v___x_917_, 0, v___x_924_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_auxDeclToFullName_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_931_, lean_object* v_newDecl_932_){
_start:
{
lean_object* v_decls_933_; lean_object* v_fvarIdToDecl_934_; lean_object* v_auxDeclToFullName_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_950_; 
v_decls_933_ = lean_ctor_get(v_lctx_931_, 1);
v_fvarIdToDecl_934_ = lean_ctor_get(v_lctx_931_, 0);
v_auxDeclToFullName_935_ = lean_ctor_get(v_lctx_931_, 2);
v_isSharedCheck_950_ = !lean_is_exclusive(v_lctx_931_);
if (v_isSharedCheck_950_ == 0)
{
v___x_937_ = v_lctx_931_;
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_auxDeclToFullName_935_);
lean_inc(v_decls_933_);
lean_inc(v_fvarIdToDecl_934_);
lean_dec(v_lctx_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_950_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_size_939_; lean_object* v_newDecl_940_; lean_object* v___y_942_; lean_object* v_fvarId_949_; 
v_size_939_ = lean_ctor_get(v_decls_933_, 2);
lean_inc(v_size_939_);
v_newDecl_940_ = l_Lean_LocalDecl_setIndex(v_newDecl_932_, v_size_939_);
v_fvarId_949_ = lean_ctor_get(v_newDecl_940_, 1);
lean_inc(v_fvarId_949_);
v___y_942_ = v_fvarId_949_;
goto v___jp_941_;
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_inc_ref(v_newDecl_940_);
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_934_, v___y_942_, v_newDecl_940_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_newDecl_940_);
v___x_945_ = l_Lean_PersistentArray_push___redArg(v_decls_933_, v___x_944_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_945_);
lean_ctor_set(v___x_937_, 0, v___x_943_);
v___x_947_ = v___x_937_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_auxDeclToFullName_935_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_array_get_size(v_keys_951_);
v___x_956_ = lean_nat_dec_lt(v_i_953_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v_i_953_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
lean_object* v_k_x27_958_; uint8_t v___x_959_; 
v_k_x27_958_ = lean_array_fget_borrowed(v_keys_951_, v_i_953_);
v___x_959_ = l_Lean_instBEqFVarId_beq(v_k_954_, v_k_x27_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_i_953_, v___x_960_);
lean_dec(v_i_953_);
v_i_953_ = v___x_961_;
goto _start;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_array_fget_borrowed(v_vals_952_, v_i_953_);
lean_dec(v_i_953_);
lean_inc(v___x_963_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_i_967_, lean_object* v_k_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_965_, v_vals_966_, v_i_967_, v_k_968_);
lean_dec(v_k_968_);
lean_dec_ref(v_vals_966_);
lean_dec_ref(v_keys_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_970_, size_t v_x_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_970_) == 0)
{
lean_object* v_es_973_; lean_object* v___x_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v_j_977_; lean_object* v___x_978_; 
v_es_973_ = lean_ctor_get(v_x_970_, 0);
v___x_974_ = lean_box(2);
v___x_975_ = ((size_t)31ULL);
v___x_976_ = lean_usize_land(v_x_971_, v___x_975_);
v_j_977_ = lean_usize_to_nat(v___x_976_);
v___x_978_ = lean_array_get_borrowed(v___x_974_, v_es_973_, v_j_977_);
lean_dec(v_j_977_);
switch(lean_obj_tag(v___x_978_))
{
case 0:
{
lean_object* v_key_979_; lean_object* v_val_980_; uint8_t v___x_981_; 
v_key_979_ = lean_ctor_get(v___x_978_, 0);
v_val_980_ = lean_ctor_get(v___x_978_, 1);
v___x_981_ = l_Lean_instBEqFVarId_beq(v_x_972_, v_key_979_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_box(0);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
lean_inc(v_val_980_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_val_980_);
return v___x_983_;
}
}
case 1:
{
lean_object* v_node_984_; size_t v___x_985_; size_t v___x_986_; 
v_node_984_ = lean_ctor_get(v___x_978_, 0);
v___x_985_ = ((size_t)5ULL);
v___x_986_ = lean_usize_shift_right(v_x_971_, v___x_985_);
v_x_970_ = v_node_984_;
v_x_971_ = v___x_986_;
goto _start;
}
default: 
{
lean_object* v___x_988_; 
v___x_988_ = lean_box(0);
return v___x_988_;
}
}
}
else
{
lean_object* v_ks_989_; lean_object* v_vs_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_ks_989_ = lean_ctor_get(v_x_970_, 0);
v_vs_990_ = lean_ctor_get(v_x_970_, 1);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_989_, v_vs_990_, v___x_991_, v_x_972_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_135__boxed_996_; lean_object* v_res_997_; 
v_x_135__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_993_, v_x_135__boxed_996_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_x_993_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
uint64_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = l_Lean_instHashableFVarId_hash(v_x_999_);
v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
v___x_1002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_998_, v___x_1001_, v_x_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1003_, v_x_1004_);
lean_dec(v_x_1004_);
lean_dec_ref(v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1006_, lean_object* v_fvarId_1007_){
_start:
{
lean_object* v_fvarIdToDecl_1008_; lean_object* v___x_1009_; 
v_fvarIdToDecl_1008_ = lean_ctor_get(v_lctx_1006_, 0);
lean_inc_ref(v_fvarIdToDecl_1008_);
lean_dec_ref(v_lctx_1006_);
v___x_1009_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1008_, v_fvarId_1007_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_fvarIdToDecl_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1014_, v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec_ref(v_x_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, size_t v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1019_, v_x_1020_, v_x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
size_t v_x_204__boxed_1027_; lean_object* v_res_1028_; 
v_x_204__boxed_1027_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1028_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1023_, v_x_1024_, v_x_204__boxed_1027_, v_x_1026_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1024_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1030_, v_vals_1031_, v_i_1033_, v_k_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1036_, v_keys_1037_, v_vals_1038_, v_heq_1039_, v_i_1040_, v_k_1041_);
lean_dec(v_k_1041_);
lean_dec_ref(v_vals_1038_);
lean_dec_ref(v_keys_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lean_Expr_fvarId_x21(v_e_1044_);
v___x_1046_ = lean_local_ctx_find(v_lctx_1043_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1047_, lean_object* v_e_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1047_, v_e_1048_);
lean_dec_ref(v_e_1048_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1053_ = lean_unsigned_to_nat(14u);
v___x_1054_ = lean_unsigned_to_nat(339u);
v___x_1055_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1056_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1057_ = l_mkPanicMessageWithDecl(v___x_1056_, v___x_1055_, v___x_1054_, v___x_1053_, v___x_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1058_, lean_object* v_fvarId_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_local_ctx_find(v_lctx_1058_, v_fvarId_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1062_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v_val_1063_; 
v_val_1063_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v___x_1060_, 1);
return v_val_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1064_, lean_object* v_e_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_Expr_fvarId_x21(v_e_1065_);
v___x_1067_ = l_Lean_LocalContext_get_x21(v_lctx_1064_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1068_, lean_object* v_e_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1068_, v_e_1069_);
lean_dec_ref(v_e_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_array_get_size(v_keys_1071_);
v___x_1075_ = lean_nat_dec_lt(v_i_1072_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec(v_i_1072_);
return v___x_1075_;
}
else
{
lean_object* v_k_x27_1076_; uint8_t v___x_1077_; 
v_k_x27_1076_ = lean_array_fget_borrowed(v_keys_1071_, v_i_1072_);
v___x_1077_ = l_Lean_instBEqFVarId_beq(v_k_1073_, v_k_x27_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_i_1072_, v___x_1078_);
lean_dec(v_i_1072_);
v_i_1072_ = v___x_1079_;
goto _start;
}
else
{
lean_dec(v_i_1072_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1081_, lean_object* v_i_1082_, lean_object* v_k_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1081_, v_i_1082_, v_k_1083_);
lean_dec(v_k_1083_);
lean_dec_ref(v_keys_1081_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_es_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_j_1093_; lean_object* v___x_1094_; 
v_es_1089_ = lean_ctor_get(v_x_1086_, 0);
v___x_1090_ = lean_box(2);
v___x_1091_ = ((size_t)31ULL);
v___x_1092_ = lean_usize_land(v_x_1087_, v___x_1091_);
v_j_1093_ = lean_usize_to_nat(v___x_1092_);
v___x_1094_ = lean_array_get_borrowed(v___x_1090_, v_es_1089_, v_j_1093_);
lean_dec(v_j_1093_);
switch(lean_obj_tag(v___x_1094_))
{
case 0:
{
lean_object* v_key_1095_; uint8_t v___x_1096_; 
v_key_1095_ = lean_ctor_get(v___x_1094_, 0);
v___x_1096_ = l_Lean_instBEqFVarId_beq(v_x_1088_, v_key_1095_);
return v___x_1096_;
}
case 1:
{
lean_object* v_node_1097_; size_t v___x_1098_; size_t v___x_1099_; 
v_node_1097_ = lean_ctor_get(v___x_1094_, 0);
v___x_1098_ = ((size_t)5ULL);
v___x_1099_ = lean_usize_shift_right(v_x_1087_, v___x_1098_);
v_x_1086_ = v_node_1097_;
v_x_1087_ = v___x_1099_;
goto _start;
}
default: 
{
uint8_t v___x_1101_; 
v___x_1101_ = 0;
return v___x_1101_;
}
}
}
else
{
lean_object* v_ks_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_ks_1102_ = lean_ctor_get(v_x_1086_, 0);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1102_, v___x_1103_, v_x_1088_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_119__boxed_1108_; uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_x_119__boxed_1108_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1109_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1105_, v_x_119__boxed_1108_, v_x_1107_);
lean_dec(v_x_1107_);
lean_dec_ref(v_x_1105_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
uint64_t v___x_1113_; size_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = l_Lean_instHashableFVarId_hash(v_x_1112_);
v___x_1114_ = lean_uint64_to_usize(v___x_1113_);
v___x_1115_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1111_, v___x_1114_, v_x_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1116_, v_x_1117_);
lean_dec(v_x_1117_);
lean_dec_ref(v_x_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1120_, lean_object* v_fvarId_1121_){
_start:
{
lean_object* v_fvarIdToDecl_1122_; uint8_t v___x_1123_; 
v_fvarIdToDecl_1122_ = lean_ctor_get(v_lctx_1120_, 0);
v___x_1123_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1122_, v_fvarId_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1124_, lean_object* v_fvarId_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Lean_LocalContext_contains(v_lctx_1124_, v_fvarId_1125_);
lean_dec(v_fvarId_1125_);
lean_dec_ref(v_lctx_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1129_, v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1132_, v_x_1133_, v_x_1134_);
lean_dec(v_x_1134_);
lean_dec_ref(v_x_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, size_t v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1138_, v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
size_t v_x_182__boxed_1146_; uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_x_182__boxed_1146_ = lean_unbox_usize(v_x_1144_);
lean_dec(v_x_1144_);
v_res_1147_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1142_, v_x_1143_, v_x_182__boxed_1146_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec_ref(v_x_1143_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_k_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1150_, v_i_1153_, v_k_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_heq_1159_, lean_object* v_i_1160_, lean_object* v_k_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1156_, v_keys_1157_, v_vals_1158_, v_heq_1159_, v_i_1160_, v_k_1161_);
lean_dec(v_k_1161_);
lean_dec_ref(v_vals_1158_);
lean_dec_ref(v_keys_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1164_, lean_object* v_e_1165_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = l_Lean_Expr_fvarId_x21(v_e_1165_);
v___x_1167_ = l_Lean_LocalContext_contains(v_lctx_1164_, v___x_1166_);
lean_dec(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1168_, lean_object* v_e_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Lean_LocalContext_containsFVar(v_lctx_1168_, v_e_1169_);
lean_dec_ref(v_e_1169_);
lean_dec_ref(v_lctx_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1172_, size_t v_i_1173_, size_t v_stop_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v___y_1177_; uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_eq(v_i_1173_, v_stop_1174_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_array_uget_borrowed(v_as_1172_, v_i_1173_);
if (lean_obj_tag(v___x_1182_) == 0)
{
v___y_1177_ = v_b_1175_;
goto v___jp_1176_;
}
else
{
lean_object* v_val_1183_; lean_object* v_fvarId_1184_; lean_object* v___x_1185_; 
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
v_fvarId_1184_ = lean_ctor_get(v_val_1183_, 1);
lean_inc(v_fvarId_1184_);
v___x_1185_ = lean_array_push(v_b_1175_, v_fvarId_1184_);
v___y_1177_ = v___x_1185_;
goto v___jp_1176_;
}
}
else
{
return v_b_1175_;
}
v___jp_1176_:
{
size_t v___x_1178_; size_t v___x_1179_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1173_, v___x_1178_);
v_i_1173_ = v___x_1179_;
v_b_1175_ = v___y_1177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_stop_1188_, lean_object* v_b_1189_){
_start:
{
size_t v_i_boxed_1190_; size_t v_stop_boxed_1191_; lean_object* v_res_1192_; 
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_stop_boxed_1191_ = lean_unbox_usize(v_stop_1188_);
lean_dec(v_stop_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1186_, v_i_boxed_1190_, v_stop_boxed_1191_, v_b_1189_);
lean_dec_ref(v_as_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_cs_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_cs_1195_ = lean_ctor_get(v_x_1193_, 0);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_cs_1195_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
return v_x_1194_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1197_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1195_, v___x_1199_, v___x_1200_, v_x_1194_);
return v___x_1201_;
}
}
else
{
lean_object* v_vs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_vs_1202_ = lean_ctor_get(v_x_1193_, 0);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_vs_1202_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v_x_1194_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1204_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1202_, v___x_1206_, v___x_1207_, v_x_1194_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v___x_1214_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
v___x_1215_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1214_, v_b_1212_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1210_, v___x_1216_);
v_i_1210_ = v___x_1217_;
v_b_1212_ = v___x_1215_;
goto _start;
}
else
{
return v_b_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1219_, lean_object* v_i_1220_, lean_object* v_stop_1221_, lean_object* v_b_1222_){
_start:
{
size_t v_i_boxed_1223_; size_t v_stop_boxed_1224_; lean_object* v_res_1225_; 
v_i_boxed_1223_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_stop_boxed_1224_ = lean_unbox_usize(v_stop_1221_);
lean_dec(v_stop_1221_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1219_, v_i_boxed_1223_, v_stop_boxed_1224_, v_b_1222_);
lean_dec_ref(v_as_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1226_, v_x_1227_);
lean_dec_ref(v_x_1226_);
return v_res_1228_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1230_, size_t v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_cs_1234_; lean_object* v___x_1235_; size_t v___x_1236_; lean_object* v_j_1237_; lean_object* v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_cs_1234_ = lean_ctor_get(v_x_1230_, 0);
v___x_1235_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1236_ = lean_usize_shift_right(v_x_1231_, v_x_1232_);
v_j_1237_ = lean_usize_to_nat(v___x_1236_);
v___x_1238_ = lean_array_get_borrowed(v___x_1235_, v_cs_1234_, v_j_1237_);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_shift_left(v___x_1239_, v_x_1232_);
v___x_1241_ = lean_usize_sub(v___x_1240_, v___x_1239_);
v___x_1242_ = lean_usize_land(v_x_1231_, v___x_1241_);
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_usize_sub(v_x_1232_, v___x_1243_);
v___x_1245_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1238_, v___x_1242_, v___x_1244_, v_x_1233_);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_j_1237_, v___x_1246_);
lean_dec(v_j_1237_);
v___x_1248_ = lean_array_get_size(v_cs_1234_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v___x_1247_);
return v___x_1245_;
}
else
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_usize_of_nat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_usize_of_nat(v___x_1248_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1234_, v___x_1250_, v___x_1251_, v___x_1245_);
return v___x_1252_;
}
}
else
{
lean_object* v_vs_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_vs_1253_ = lean_ctor_get(v_x_1230_, 0);
v___x_1254_ = lean_usize_to_nat(v_x_1231_);
v___x_1255_ = lean_array_get_size(v_vs_1253_);
v___x_1256_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v___x_1254_);
return v_x_1233_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_usize_of_nat(v___x_1255_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1253_, v___x_1257_, v___x_1258_, v_x_1233_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_1260__boxed_1264_; size_t v_x_1261__boxed_1265_; lean_object* v_res_1266_; 
v_x_1260__boxed_1264_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_x_1261__boxed_1265_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_res_1266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1260_, v_x_1260__boxed_1264_, v_x_1261__boxed_1265_, v_x_1263_);
lean_dec_ref(v_x_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1267_, lean_object* v_init_1268_, lean_object* v_start_1269_){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_nat_dec_eq(v_start_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v_root_1272_; lean_object* v_tail_1273_; size_t v_shift_1274_; lean_object* v_tailOff_1275_; uint8_t v___x_1276_; 
v_root_1272_ = lean_ctor_get(v_t_1267_, 0);
v_tail_1273_ = lean_ctor_get(v_t_1267_, 1);
v_shift_1274_ = lean_ctor_get_usize(v_t_1267_, 4);
v_tailOff_1275_ = lean_ctor_get(v_t_1267_, 3);
v___x_1276_ = lean_nat_dec_le(v_tailOff_1275_, v_start_1269_);
if (v___x_1276_ == 0)
{
size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1277_ = lean_usize_of_nat(v_start_1269_);
v___x_1278_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1272_, v___x_1277_, v_shift_1274_, v_init_1268_);
v___x_1279_ = lean_array_get_size(v_tail_1273_);
v___x_1280_ = lean_nat_dec_lt(v___x_1270_, v___x_1279_);
if (v___x_1280_ == 0)
{
return v___x_1278_;
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1279_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1273_, v___x_1281_, v___x_1282_, v___x_1278_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_nat_sub(v_start_1269_, v_tailOff_1275_);
v___x_1285_ = lean_array_get_size(v_tail_1273_);
v___x_1286_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1284_);
return v_init_1268_;
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_usize_of_nat(v___x_1284_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_usize_of_nat(v___x_1285_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1273_, v___x_1287_, v___x_1288_, v_init_1268_);
return v___x_1289_;
}
}
}
else
{
lean_object* v_root_1290_; lean_object* v_tail_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_root_1290_ = lean_ctor_get(v_t_1267_, 0);
v_tail_1291_ = lean_ctor_get(v_t_1267_, 1);
v___x_1292_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1290_, v_init_1268_);
v___x_1293_ = lean_array_get_size(v_tail_1291_);
v___x_1294_ = lean_nat_dec_lt(v___x_1270_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1292_;
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1293_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1295_, v___x_1296_, v___x_1292_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1298_, lean_object* v_init_1299_, lean_object* v_start_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1298_, v_init_1299_, v_start_1300_);
lean_dec(v_start_1300_);
lean_dec_ref(v_t_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1304_){
_start:
{
lean_object* v_decls_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_decls_1305_ = lean_ctor_get(v_lctx_1304_, 1);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1308_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1305_, v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_LocalContext_getFVarIds(v_lctx_1309_);
lean_dec_ref(v_lctx_1309_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_bs_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1312_, v_sz_1311_);
if (v___x_1314_ == 0)
{
return v_bs_1313_;
}
else
{
lean_object* v_v_1315_; lean_object* v___x_1316_; lean_object* v_bs_x27_1317_; lean_object* v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v_v_1315_ = lean_array_uget(v_bs_1313_, v_i_1312_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v_bs_x27_1317_ = lean_array_uset(v_bs_1313_, v_i_1312_, v___x_1316_);
v___x_1318_ = l_Lean_mkFVar(v_v_1315_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_add(v_i_1312_, v___x_1319_);
v___x_1321_ = lean_array_uset(v_bs_x27_1317_, v_i_1312_, v___x_1318_);
v_i_1312_ = v___x_1320_;
v_bs_1313_ = v___x_1321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_bs_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1326_, v_i_boxed_1327_, v_bs_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1329_){
_start:
{
lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1330_ = l_Lean_LocalContext_getFVarIds(v_lctx_1329_);
v_sz_1331_ = lean_array_size(v___x_1330_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1331_, v___x_1332_, v___x_1330_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_LocalContext_getFVars(v_lctx_1334_);
lean_dec_ref(v_lctx_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1336_){
_start:
{
lean_object* v_size_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_size_1337_ = lean_ctor_get(v_a_1336_, 2);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_nat_dec_eq(v_size_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_sub(v_size_1337_, v___x_1341_);
v___x_1343_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1340_, v_a_1336_, v___x_1342_);
lean_dec(v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_PersistentArray_pop___redArg(v_a_1336_);
v_a_1336_ = v___x_1344_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1343_, 1);
return v_a_1336_;
}
}
else
{
return v_a_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1346_, lean_object* v_t_1347_){
_start:
{
if (lean_obj_tag(v_t_1347_) == 0)
{
lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v_l_1350_; lean_object* v_r_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_2005_; 
v_k_1348_ = lean_ctor_get(v_t_1347_, 1);
v_v_1349_ = lean_ctor_get(v_t_1347_, 2);
v_l_1350_ = lean_ctor_get(v_t_1347_, 3);
v_r_1351_ = lean_ctor_get(v_t_1347_, 4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_t_1347_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_t_1347_, 0);
lean_dec(v_unused_2006_);
v___x_1353_ = v_t_1347_;
v_isShared_1354_ = v_isSharedCheck_2005_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_r_1351_);
lean_inc(v_l_1350_);
lean_inc(v_v_1349_);
lean_inc(v_k_1348_);
lean_dec(v_t_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_2005_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; 
v___x_1355_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1346_, v_k_1348_);
switch(v___x_1355_)
{
case 0:
{
lean_object* v_impl_1356_; lean_object* v___x_1357_; 
v_impl_1356_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1346_, v_l_1350_);
v___x_1357_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1356_) == 0)
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_size_1358_; lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_l_1362_; lean_object* v_r_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_size_1358_ = lean_ctor_get(v_impl_1356_, 0);
lean_inc(v_size_1358_);
v_size_1359_ = lean_ctor_get(v_r_1351_, 0);
v_k_1360_ = lean_ctor_get(v_r_1351_, 1);
v_v_1361_ = lean_ctor_get(v_r_1351_, 2);
v_l_1362_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1362_);
v_r_1363_ = lean_ctor_get(v_r_1351_, 4);
v___x_1364_ = lean_unsigned_to_nat(3u);
v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1358_);
v___x_1366_ = lean_nat_dec_lt(v___x_1365_, v_size_1359_);
lean_dec(v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec(v_l_1362_);
v___x_1367_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1368_ = lean_nat_add(v___x_1367_, v_size_1359_);
lean_dec(v___x_1367_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1368_);
v___x_1370_ = v___x_1353_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_r_1351_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1435_; 
lean_inc(v_r_1363_);
lean_inc(v_v_1361_);
lean_inc(v_k_1360_);
lean_inc(v_size_1359_);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1436_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1440_);
v___x_1373_ = v_r_1351_;
v_isShared_1374_ = v_isSharedCheck_1435_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_r_1351_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1435_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_size_1375_; lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v_l_1378_; lean_object* v_r_1379_; lean_object* v_size_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_size_1375_ = lean_ctor_get(v_l_1362_, 0);
v_k_1376_ = lean_ctor_get(v_l_1362_, 1);
v_v_1377_ = lean_ctor_get(v_l_1362_, 2);
v_l_1378_ = lean_ctor_get(v_l_1362_, 3);
v_r_1379_ = lean_ctor_get(v_l_1362_, 4);
v_size_1380_ = lean_ctor_get(v_r_1363_, 0);
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = lean_nat_mul(v___x_1381_, v_size_1380_);
v___x_1383_ = lean_nat_dec_lt(v_size_1375_, v___x_1382_);
lean_dec(v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1411_; 
lean_inc(v_r_1379_);
lean_inc(v_l_1378_);
lean_inc(v_v_1377_);
lean_inc(v_k_1376_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_l_1362_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; 
v_unused_1412_ = lean_ctor_get(v_l_1362_, 4);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_l_1362_, 3);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_l_1362_, 2);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_l_1362_, 1);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_l_1362_, 0);
lean_dec(v_unused_1416_);
v___x_1385_ = v_l_1362_;
v_isShared_1386_ = v_isSharedCheck_1411_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v_l_1362_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1411_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1401_; 
v___x_1387_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1388_ = lean_nat_add(v___x_1387_, v_size_1359_);
lean_dec(v_size_1359_);
if (lean_obj_tag(v_l_1378_) == 0)
{
lean_object* v_size_1409_; 
v_size_1409_ = lean_ctor_get(v_l_1378_, 0);
lean_inc(v_size_1409_);
v___y_1401_ = v_size_1409_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_unsigned_to_nat(0u);
v___y_1401_ = v___x_1410_;
goto v___jp_1400_;
}
v___jp_1389_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_nat_add(v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec(v___y_1391_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 4, v_r_1363_);
lean_ctor_set(v___x_1385_, 3, v_r_1379_);
lean_ctor_set(v___x_1385_, 2, v_v_1361_);
lean_ctor_set(v___x_1385_, 1, v_k_1360_);
lean_ctor_set(v___x_1385_, 0, v___x_1393_);
v___x_1395_ = v___x_1385_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_r_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_r_1363_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v___x_1395_);
lean_ctor_set(v___x_1373_, 3, v___y_1390_);
lean_ctor_set(v___x_1373_, 2, v_v_1377_);
lean_ctor_set(v___x_1373_, 1, v_k_1376_);
lean_ctor_set(v___x_1373_, 0, v___x_1388_);
v___x_1397_ = v___x_1373_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___y_1390_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
v___jp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_nat_add(v___x_1387_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec(v___x_1387_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1378_);
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1402_);
v___x_1404_ = v___x_1353_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_l_1378_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_nat_add(v___x_1357_, v_size_1380_);
if (lean_obj_tag(v_r_1379_) == 0)
{
lean_object* v_size_1406_; 
v_size_1406_ = lean_ctor_get(v_r_1379_, 0);
lean_inc(v_size_1406_);
v___y_1390_ = v___x_1404_;
v___y_1391_ = v___x_1405_;
v___y_1392_ = v_size_1406_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___y_1390_ = v___x_1404_;
v___y_1391_ = v___x_1405_;
v___y_1392_ = v___x_1407_;
goto v___jp_1389_;
}
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_del_object(v___x_1353_);
v___x_1417_ = lean_nat_add(v___x_1357_, v_size_1358_);
lean_dec(v_size_1358_);
v___x_1418_ = lean_nat_add(v___x_1417_, v_size_1359_);
lean_dec(v_size_1359_);
v___x_1419_ = lean_nat_add(v___x_1417_, v_size_1375_);
lean_dec(v___x_1417_);
lean_inc_ref(v_impl_1356_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_l_1362_);
lean_ctor_set(v___x_1373_, 3, v_impl_1356_);
lean_ctor_set(v___x_1373_, 2, v_v_1349_);
lean_ctor_set(v___x_1373_, 1, v_k_1348_);
lean_ctor_set(v___x_1373_, 0, v___x_1419_);
v___x_1421_ = v___x_1373_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_l_1362_);
v___x_1421_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_isSharedCheck_1428_ = !lean_is_exclusive(v_impl_1356_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; 
v_unused_1429_ = lean_ctor_get(v_impl_1356_, 4);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_impl_1356_, 3);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_impl_1356_, 2);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_impl_1356_, 1);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_impl_1356_, 0);
lean_dec(v_unused_1433_);
v___x_1423_ = v_impl_1356_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v_impl_1356_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1363_);
lean_ctor_set(v___x_1423_, 3, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v_v_1361_);
lean_ctor_set(v___x_1423_, 1, v_k_1360_);
lean_ctor_set(v___x_1423_, 0, v___x_1418_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_r_1363_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_size_1441_ = lean_ctor_get(v_impl_1356_, 0);
lean_inc(v_size_1441_);
v___x_1442_ = lean_nat_add(v___x_1357_, v_size_1441_);
lean_dec(v_size_1441_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_impl_1356_);
lean_ctor_set(v___x_1353_, 0, v___x_1442_);
v___x_1444_ = v___x_1353_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1351_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_l_1446_; 
v_l_1446_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1446_);
if (lean_obj_tag(v_l_1446_) == 0)
{
lean_object* v_r_1447_; 
v_r_1447_ = lean_ctor_get(v_r_1351_, 4);
lean_inc(v_r_1447_);
if (lean_obj_tag(v_r_1447_) == 0)
{
lean_object* v_size_1448_; lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1463_; 
v_size_1448_ = lean_ctor_get(v_r_1351_, 0);
v_k_1449_ = lean_ctor_get(v_r_1351_, 1);
v_v_1450_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1464_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1465_);
v___x_1452_ = v_r_1351_;
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_v_1450_);
lean_inc(v_k_1449_);
lean_inc(v_size_1448_);
lean_dec(v_r_1351_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_size_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v_size_1454_ = lean_ctor_get(v_l_1446_, 0);
v___x_1455_ = lean_nat_add(v___x_1357_, v_size_1448_);
lean_dec(v_size_1448_);
v___x_1456_ = lean_nat_add(v___x_1357_, v_size_1454_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v_l_1446_);
lean_ctor_set(v___x_1452_, 3, v_impl_1356_);
lean_ctor_set(v___x_1452_, 2, v_v_1349_);
lean_ctor_set(v___x_1452_, 1, v_k_1348_);
lean_ctor_set(v___x_1452_, 0, v___x_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_impl_1356_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_l_1446_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1447_);
lean_ctor_set(v___x_1353_, 3, v___x_1458_);
lean_ctor_set(v___x_1353_, 2, v_v_1450_);
lean_ctor_set(v___x_1353_, 1, v_k_1449_);
lean_ctor_set(v___x_1353_, 0, v___x_1455_);
v___x_1460_ = v___x_1353_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1447_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1490_; 
v_k_1466_ = lean_ctor_get(v_r_1351_, 1);
v_v_1467_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1491_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1493_);
v___x_1469_ = v_r_1351_;
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_r_1351_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1490_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1486_; 
v_k_1471_ = lean_ctor_get(v_l_1446_, 1);
v_v_1472_ = lean_ctor_get(v_l_1446_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_l_1446_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1487_ = lean_ctor_get(v_l_1446_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1446_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_l_1446_, 0);
lean_dec(v_unused_1489_);
v___x_1474_ = v_l_1446_;
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_dec(v_l_1446_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_unsigned_to_nat(3u);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v_r_1447_);
lean_ctor_set(v___x_1474_, 3, v_r_1447_);
lean_ctor_set(v___x_1474_, 2, v_v_1349_);
lean_ctor_set(v___x_1474_, 1, v_k_1348_);
lean_ctor_set(v___x_1474_, 0, v___x_1357_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1447_);
v___x_1478_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 3, v_r_1447_);
lean_ctor_set(v___x_1469_, 0, v___x_1357_);
v___x_1480_ = v___x_1469_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1447_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1480_);
lean_ctor_set(v___x_1353_, 3, v___x_1478_);
lean_ctor_set(v___x_1353_, 2, v_v_1472_);
lean_ctor_set(v___x_1353_, 1, v_k_1471_);
lean_ctor_set(v___x_1353_, 0, v___x_1476_);
v___x_1482_ = v___x_1353_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1494_; 
v_r_1494_ = lean_ctor_get(v_r_1351_, 4);
lean_inc(v_r_1494_);
if (lean_obj_tag(v_r_1494_) == 0)
{
lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1507_; 
v_k_1495_ = lean_ctor_get(v_r_1351_, 1);
v_v_1496_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1508_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1510_);
v___x_1498_ = v_r_1351_;
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_v_1496_);
lean_inc(v_k_1495_);
lean_dec(v_r_1351_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_unsigned_to_nat(3u);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v_l_1446_);
lean_ctor_set(v___x_1498_, 2, v_v_1349_);
lean_ctor_set(v___x_1498_, 1, v_k_1348_);
lean_ctor_set(v___x_1498_, 0, v___x_1357_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_l_1446_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_l_1446_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1494_);
lean_ctor_set(v___x_1353_, 3, v___x_1502_);
lean_ctor_set(v___x_1353_, 2, v_v_1496_);
lean_ctor_set(v___x_1353_, 1, v_k_1495_);
lean_ctor_set(v___x_1353_, 0, v___x_1500_);
v___x_1504_ = v___x_1353_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_k_1495_);
lean_ctor_set(v_reuseFailAlloc_1505_, 2, v_v_1496_);
lean_ctor_set(v_reuseFailAlloc_1505_, 3, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1505_, 4, v_r_1494_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_size_1511_; lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1524_; 
v_size_1511_ = lean_ctor_get(v_r_1351_, 0);
v_k_1512_ = lean_ctor_get(v_r_1351_, 1);
v_v_1513_ = lean_ctor_get(v_r_1351_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1525_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1526_);
v___x_1515_ = v_r_1351_;
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
lean_inc(v_size_1511_);
lean_dec(v_r_1351_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1524_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 3, v_r_1494_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_size_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_r_1494_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_r_1494_);
v___x_1518_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(2u);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1518_);
lean_ctor_set(v___x_1353_, 3, v_r_1494_);
lean_ctor_set(v___x_1353_, 0, v___x_1519_);
v___x_1521_ = v___x_1353_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_r_1494_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1518_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
else
{
lean_object* v___x_1528_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 3, v_r_1351_);
lean_ctor_set(v___x_1353_, 0, v___x_1357_);
v___x_1528_ = v___x_1353_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_r_1351_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1351_);
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
case 1:
{
lean_del_object(v___x_1353_);
lean_dec(v_v_1349_);
lean_dec(v_k_1348_);
if (lean_obj_tag(v_l_1350_) == 0)
{
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v_l_1533_; lean_object* v_r_1534_; lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_l_1538_; lean_object* v_r_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_size_1530_ = lean_ctor_get(v_l_1350_, 0);
v_k_1531_ = lean_ctor_get(v_l_1350_, 1);
v_v_1532_ = lean_ctor_get(v_l_1350_, 2);
v_l_1533_ = lean_ctor_get(v_l_1350_, 3);
v_r_1534_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1534_);
v_size_1535_ = lean_ctor_get(v_r_1351_, 0);
v_k_1536_ = lean_ctor_get(v_r_1351_, 1);
v_v_1537_ = lean_ctor_get(v_r_1351_, 2);
v_l_1538_ = lean_ctor_get(v_r_1351_, 3);
lean_inc(v_l_1538_);
v_r_1539_ = lean_ctor_get(v_r_1351_, 4);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_dec_lt(v_size_1530_, v_size_1535_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1678_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1682_);
v___x_1543_ = v_l_1350_;
v_isShared_1544_ = v_isSharedCheck_1677_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_l_1350_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1677_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v_tree_1546_; 
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1531_, v_v_1532_, v_l_1533_, v_r_1534_);
v_tree_1546_ = lean_ctor_get(v___x_1545_, 2);
lean_inc(v_tree_1546_);
if (lean_obj_tag(v_tree_1546_) == 0)
{
lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v_size_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_k_1547_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1547_);
v_v_1548_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1548_);
lean_dec_ref(v___x_1545_);
v_size_1549_ = lean_ctor_get(v_tree_1546_, 0);
v___x_1550_ = lean_unsigned_to_nat(3u);
v___x_1551_ = lean_nat_mul(v___x_1550_, v_size_1549_);
v___x_1552_ = lean_nat_dec_lt(v___x_1551_, v_size_1535_);
lean_dec(v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_dec(v_l_1538_);
v___x_1553_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1554_ = lean_nat_add(v___x_1553_, v_size_1535_);
lean_dec(v___x_1553_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1351_);
lean_ctor_set(v___x_1543_, 3, v_tree_1546_);
lean_ctor_set(v___x_1543_, 2, v_v_1548_);
lean_ctor_set(v___x_1543_, 1, v_k_1547_);
lean_ctor_set(v___x_1543_, 0, v___x_1554_);
v___x_1556_ = v___x_1543_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_r_1351_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
else
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1612_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1617_);
v___x_1559_ = v_r_1351_;
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_r_1351_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_size_1561_; lean_object* v_k_1562_; lean_object* v_v_1563_; lean_object* v_l_1564_; lean_object* v_r_1565_; lean_object* v_size_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_size_1561_ = lean_ctor_get(v_l_1538_, 0);
v_k_1562_ = lean_ctor_get(v_l_1538_, 1);
v_v_1563_ = lean_ctor_get(v_l_1538_, 2);
v_l_1564_ = lean_ctor_get(v_l_1538_, 3);
v_r_1565_ = lean_ctor_get(v_l_1538_, 4);
v_size_1566_ = lean_ctor_get(v_r_1539_, 0);
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_nat_mul(v___x_1567_, v_size_1566_);
v___x_1569_ = lean_nat_dec_lt(v_size_1561_, v___x_1568_);
lean_dec(v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1597_; 
lean_inc(v_r_1565_);
lean_inc(v_l_1564_);
lean_inc(v_v_1563_);
lean_inc(v_k_1562_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_l_1538_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1598_ = lean_ctor_get(v_l_1538_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_l_1538_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_l_1538_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_l_1538_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_l_1538_, 0);
lean_dec(v_unused_1602_);
v___x_1571_ = v_l_1538_;
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_l_1538_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1587_; 
v___x_1573_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1574_ = lean_nat_add(v___x_1573_, v_size_1535_);
lean_dec(v_size_1535_);
if (lean_obj_tag(v_l_1564_) == 0)
{
lean_object* v_size_1595_; 
v_size_1595_ = lean_ctor_get(v_l_1564_, 0);
lean_inc(v_size_1595_);
v___y_1587_ = v_size_1595_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___y_1587_ = v___x_1596_;
goto v___jp_1586_;
}
v___jp_1575_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_nat_add(v___y_1576_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec(v___y_1576_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v_r_1539_);
lean_ctor_set(v___x_1571_, 3, v_r_1565_);
lean_ctor_set(v___x_1571_, 2, v_v_1537_);
lean_ctor_set(v___x_1571_, 1, v_k_1536_);
lean_ctor_set(v___x_1571_, 0, v___x_1579_);
v___x_1581_ = v___x_1571_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_r_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1539_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v___x_1581_);
lean_ctor_set(v___x_1559_, 3, v___y_1577_);
lean_ctor_set(v___x_1559_, 2, v_v_1563_);
lean_ctor_set(v___x_1559_, 1, v_k_1562_);
lean_ctor_set(v___x_1559_, 0, v___x_1574_);
v___x_1583_ = v___x_1559_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1562_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1563_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v___y_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_nat_add(v___x_1573_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec(v___x_1573_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_l_1564_);
lean_ctor_set(v___x_1543_, 3, v_tree_1546_);
lean_ctor_set(v___x_1543_, 2, v_v_1548_);
lean_ctor_set(v___x_1543_, 1, v_k_1547_);
lean_ctor_set(v___x_1543_, 0, v___x_1588_);
v___x_1590_ = v___x_1543_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_l_1564_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_nat_add(v___x_1540_, v_size_1566_);
if (lean_obj_tag(v_r_1565_) == 0)
{
lean_object* v_size_1592_; 
v_size_1592_ = lean_ctor_get(v_r_1565_, 0);
lean_inc(v_size_1592_);
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v_size_1592_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___y_1576_ = v___x_1591_;
v___y_1577_ = v___x_1590_;
v___y_1578_ = v___x_1593_;
goto v___jp_1575_;
}
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1603_ = lean_nat_add(v___x_1540_, v_size_1549_);
v___x_1604_ = lean_nat_add(v___x_1603_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1605_ = lean_nat_add(v___x_1603_, v_size_1561_);
lean_dec(v___x_1603_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1538_);
lean_ctor_set(v___x_1559_, 3, v_tree_1546_);
lean_ctor_set(v___x_1559_, 2, v_v_1548_);
lean_ctor_set(v___x_1559_, 1, v_k_1547_);
lean_ctor_set(v___x_1559_, 0, v___x_1605_);
v___x_1607_ = v___x_1559_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_l_1538_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1607_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1604_);
v___x_1609_ = v___x_1543_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1539_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1671_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_inc(v_size_1535_);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; 
v_unused_1672_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1676_);
v___x_1619_ = v_r_1351_;
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_r_1351_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1671_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
if (lean_obj_tag(v_l_1538_) == 0)
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_k_1621_; lean_object* v_v_1622_; lean_object* v_size_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v_k_1621_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1621_);
v_v_1622_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1622_);
lean_dec_ref(v___x_1545_);
v_size_1623_ = lean_ctor_get(v_l_1538_, 0);
v___x_1624_ = lean_nat_add(v___x_1540_, v_size_1535_);
lean_dec(v_size_1535_);
v___x_1625_ = lean_nat_add(v___x_1540_, v_size_1623_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_l_1538_);
lean_ctor_set(v___x_1619_, 3, v_tree_1546_);
lean_ctor_set(v___x_1619_, 2, v_v_1622_);
lean_ctor_set(v___x_1619_, 1, v_k_1621_);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1627_ = v___x_1619_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1621_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1622_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_tree_1546_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_l_1538_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1627_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1624_);
v___x_1629_ = v___x_1543_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_r_1539_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_k_1632_; lean_object* v_v_1633_; lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_size_1535_);
v_k_1632_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1632_);
v_v_1633_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1633_);
lean_dec_ref(v___x_1545_);
v_k_1634_ = lean_ctor_get(v_l_1538_, 1);
v_v_1635_ = lean_ctor_get(v_l_1538_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_l_1538_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1650_ = lean_ctor_get(v_l_1538_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1538_, 3);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_l_1538_, 0);
lean_dec(v_unused_1652_);
v___x_1637_ = v_l_1538_;
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_v_1635_);
lean_inc(v_k_1634_);
lean_dec(v_l_1538_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1649_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(3u);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_r_1539_);
lean_ctor_set(v___x_1637_, 3, v_r_1539_);
lean_ctor_set(v___x_1637_, 2, v_v_1633_);
lean_ctor_set(v___x_1637_, 1, v_k_1632_);
lean_ctor_set(v___x_1637_, 0, v___x_1540_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1632_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1633_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_r_1539_);
v___x_1641_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 3, v_r_1539_);
lean_ctor_set(v___x_1619_, 0, v___x_1540_);
v___x_1643_ = v___x_1619_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_r_1539_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v___x_1643_);
lean_ctor_set(v___x_1543_, 3, v___x_1641_);
lean_ctor_set(v___x_1543_, 2, v_v_1635_);
lean_ctor_set(v___x_1543_, 1, v_k_1634_);
lean_ctor_set(v___x_1543_, 0, v___x_1639_);
v___x_1645_ = v___x_1543_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1634_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_size_1535_);
v_k_1653_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1653_);
v_v_1654_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1654_);
lean_dec_ref(v___x_1545_);
v___x_1655_ = lean_unsigned_to_nat(3u);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_l_1538_);
lean_ctor_set(v___x_1619_, 2, v_v_1654_);
lean_ctor_set(v___x_1619_, 1, v_k_1653_);
lean_ctor_set(v___x_1619_, 0, v___x_1540_);
v___x_1657_ = v___x_1619_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1653_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1654_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1538_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1538_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1539_);
lean_ctor_set(v___x_1543_, 3, v___x_1657_);
lean_ctor_set(v___x_1543_, 2, v_v_1537_);
lean_ctor_set(v___x_1543_, 1, v_k_1536_);
lean_ctor_set(v___x_1543_, 0, v___x_1655_);
v___x_1659_ = v___x_1543_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1539_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v___x_1665_; 
v_k_1662_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_k_1662_);
v_v_1663_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_v_1663_);
lean_dec_ref(v___x_1545_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 3, v_r_1539_);
v___x_1665_ = v___x_1619_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_size_1535_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1539_);
v___x_1665_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(2u);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v___x_1665_);
lean_ctor_set(v___x_1543_, 3, v_r_1539_);
lean_ctor_set(v___x_1543_, 2, v_v_1663_);
lean_ctor_set(v___x_1543_, 1, v_k_1662_);
lean_ctor_set(v___x_1543_, 0, v___x_1666_);
v___x_1668_ = v___x_1543_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1665_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
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
lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1835_; 
lean_inc(v_r_1539_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_r_1351_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; 
v_unused_1836_ = lean_ctor_get(v_r_1351_, 4);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_r_1351_, 3);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_r_1351_, 2);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_r_1351_, 1);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1351_, 0);
lean_dec(v_unused_1840_);
v___x_1684_ = v_r_1351_;
v_isShared_1685_ = v_isSharedCheck_1835_;
goto v_resetjp_1683_;
}
else
{
lean_dec(v_r_1351_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1835_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v_tree_1687_; 
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1536_, v_v_1537_, v_l_1538_, v_r_1539_);
v_tree_1687_ = lean_ctor_get(v___x_1686_, 2);
lean_inc(v_tree_1687_);
if (lean_obj_tag(v_tree_1687_) == 0)
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v_size_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_k_1688_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1688_);
v_v_1689_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1689_);
lean_dec_ref(v___x_1686_);
v_size_1690_ = lean_ctor_get(v_tree_1687_, 0);
v___x_1691_ = lean_unsigned_to_nat(3u);
v___x_1692_ = lean_nat_mul(v___x_1691_, v_size_1690_);
v___x_1693_ = lean_nat_dec_lt(v___x_1692_, v_size_1530_);
lean_dec(v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec(v_r_1534_);
v___x_1694_ = lean_nat_add(v___x_1540_, v_size_1530_);
v___x_1695_ = lean_nat_add(v___x_1694_, v_size_1690_);
lean_dec(v___x_1694_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_l_1350_);
lean_ctor_set(v___x_1684_, 2, v_v_1689_);
lean_ctor_set(v___x_1684_, 1, v_k_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1695_);
v___x_1697_ = v___x_1684_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_tree_1687_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1764_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; lean_object* v_unused_1769_; 
v_unused_1765_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1769_);
v___x_1700_ = v_l_1350_;
v_isShared_1701_ = v_isSharedCheck_1764_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_l_1350_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1764_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_size_1702_; lean_object* v_size_1703_; lean_object* v_k_1704_; lean_object* v_v_1705_; lean_object* v_l_1706_; lean_object* v_r_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_size_1702_ = lean_ctor_get(v_l_1533_, 0);
v_size_1703_ = lean_ctor_get(v_r_1534_, 0);
v_k_1704_ = lean_ctor_get(v_r_1534_, 1);
v_v_1705_ = lean_ctor_get(v_r_1534_, 2);
v_l_1706_ = lean_ctor_get(v_r_1534_, 3);
v_r_1707_ = lean_ctor_get(v_r_1534_, 4);
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = lean_nat_mul(v___x_1708_, v_size_1702_);
v___x_1710_ = lean_nat_dec_lt(v_size_1703_, v___x_1709_);
lean_dec(v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1748_; 
lean_inc(v_r_1707_);
lean_inc(v_l_1706_);
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
lean_del_object(v___x_1700_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; lean_object* v_unused_1750_; lean_object* v_unused_1751_; lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1749_ = lean_ctor_get(v_r_1534_, 4);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_r_1534_, 3);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v_r_1534_, 2);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_r_1534_, 1);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_r_1534_, 0);
lean_dec(v_unused_1753_);
v___x_1712_ = v_r_1534_;
v_isShared_1713_ = v_isSharedCheck_1748_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v_r_1534_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1748_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1736_; lean_object* v___y_1738_; 
v___x_1714_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1715_ = lean_nat_add(v___x_1714_, v_size_1690_);
lean_dec(v___x_1714_);
v___x_1736_ = lean_nat_add(v___x_1540_, v_size_1702_);
if (lean_obj_tag(v_l_1706_) == 0)
{
lean_object* v_size_1746_; 
v_size_1746_ = lean_ctor_get(v_l_1706_, 0);
lean_inc(v_size_1746_);
v___y_1738_ = v_size_1746_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___y_1738_ = v___x_1747_;
goto v___jp_1737_;
}
v___jp_1716_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_nat_add(v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
lean_inc_ref(v_tree_1687_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 4, v_tree_1687_);
lean_ctor_set(v___x_1712_, 3, v_r_1707_);
lean_ctor_set(v___x_1712_, 2, v_v_1689_);
lean_ctor_set(v___x_1712_, 1, v_k_1688_);
lean_ctor_set(v___x_1712_, 0, v___x_1720_);
v___x_1722_ = v___x_1712_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_tree_1687_);
v___x_1722_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_isSharedCheck_1729_ = !lean_is_exclusive(v_tree_1687_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; 
v_unused_1730_ = lean_ctor_get(v_tree_1687_, 4);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_tree_1687_, 3);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_tree_1687_, 2);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_tree_1687_, 1);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_tree_1687_, 0);
lean_dec(v_unused_1734_);
v___x_1724_ = v_tree_1687_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_tree_1687_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v___x_1722_);
lean_ctor_set(v___x_1724_, 3, v___y_1717_);
lean_ctor_set(v___x_1724_, 2, v_v_1705_);
lean_ctor_set(v___x_1724_, 1, v_k_1704_);
lean_ctor_set(v___x_1724_, 0, v___x_1715_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v___y_1717_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v___x_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
v___jp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_nat_add(v___x_1736_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec(v___x_1736_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_l_1706_);
lean_ctor_set(v___x_1684_, 3, v_l_1533_);
lean_ctor_set(v___x_1684_, 2, v_v_1532_);
lean_ctor_set(v___x_1684_, 1, v_k_1531_);
lean_ctor_set(v___x_1684_, 0, v___x_1739_);
v___x_1741_ = v___x_1684_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_l_1706_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_nat_add(v___x_1540_, v_size_1690_);
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_size_1743_; 
v_size_1743_ = lean_ctor_get(v_r_1707_, 0);
lean_inc(v_size_1743_);
v___y_1717_ = v___x_1741_;
v___y_1718_ = v___x_1742_;
v___y_1719_ = v_size_1743_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___y_1717_ = v___x_1741_;
v___y_1718_ = v___x_1742_;
v___y_1719_ = v___x_1744_;
goto v___jp_1716_;
}
}
}
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1754_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1755_ = lean_nat_add(v___x_1754_, v_size_1690_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_nat_add(v___x_1540_, v_size_1690_);
v___x_1757_ = lean_nat_add(v___x_1756_, v_size_1703_);
lean_dec(v___x_1756_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1689_);
lean_ctor_set(v___x_1684_, 1, v_k_1688_);
lean_ctor_set(v___x_1684_, 0, v___x_1757_);
v___x_1759_ = v___x_1684_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_tree_1687_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v___x_1759_);
lean_ctor_set(v___x_1700_, 0, v___x_1755_);
v___x_1761_ = v___x_1700_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1533_) == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1793_; 
lean_inc_ref(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1794_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1798_);
v___x_1771_ = v_l_1350_;
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v_l_1350_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_k_1773_; lean_object* v_v_1774_; lean_object* v_size_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_k_1773_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1773_);
v_v_1774_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1774_);
lean_dec_ref(v___x_1686_);
v_size_1775_ = lean_ctor_get(v_r_1534_, 0);
v___x_1776_ = lean_nat_add(v___x_1540_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1777_ = lean_nat_add(v___x_1540_, v_size_1775_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_tree_1687_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1774_);
lean_ctor_set(v___x_1684_, 1, v_k_1773_);
lean_ctor_set(v___x_1684_, 0, v___x_1777_);
v___x_1779_ = v___x_1684_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_k_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_v_1774_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_tree_1687_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1779_);
lean_ctor_set(v___x_1771_, 0, v___x_1776_);
v___x_1781_ = v___x_1771_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_k_1784_; lean_object* v_v_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_size_1530_);
v_k_1784_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1784_);
v_v_1785_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1785_);
lean_dec_ref(v___x_1686_);
v___x_1786_ = lean_unsigned_to_nat(3u);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_r_1534_);
lean_ctor_set(v___x_1684_, 3, v_r_1534_);
lean_ctor_set(v___x_1684_, 2, v_v_1785_);
lean_ctor_set(v___x_1684_, 1, v_k_1784_);
lean_ctor_set(v___x_1684_, 0, v___x_1540_);
v___x_1788_ = v___x_1684_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_r_1534_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1788_);
lean_ctor_set(v___x_1771_, 0, v___x_1786_);
v___x_1790_ = v___x_1771_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1823_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; 
v_unused_1824_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1828_);
v___x_1800_ = v_l_1350_;
v_isShared_1801_ = v_isSharedCheck_1823_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v_l_1350_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1823_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_k_1802_; lean_object* v_v_1803_; lean_object* v_k_1804_; lean_object* v_v_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1819_; 
v_k_1802_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1802_);
v_v_1803_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1803_);
lean_dec_ref(v___x_1686_);
v_k_1804_ = lean_ctor_get(v_r_1534_, 1);
v_v_1805_ = lean_ctor_get(v_r_1534_, 2);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; lean_object* v_unused_1821_; lean_object* v_unused_1822_; 
v_unused_1820_ = lean_ctor_get(v_r_1534_, 4);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_r_1534_, 3);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_r_1534_, 0);
lean_dec(v_unused_1822_);
v___x_1807_ = v_r_1534_;
v_isShared_1808_ = v_isSharedCheck_1819_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_v_1805_);
lean_inc(v_k_1804_);
lean_dec(v_r_1534_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1819_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_unsigned_to_nat(3u);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 4, v_l_1533_);
lean_ctor_set(v___x_1807_, 3, v_l_1533_);
lean_ctor_set(v___x_1807_, 2, v_v_1532_);
lean_ctor_set(v___x_1807_, 1, v_k_1531_);
lean_ctor_set(v___x_1807_, 0, v___x_1540_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_l_1533_);
v___x_1811_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_l_1533_);
lean_ctor_set(v___x_1684_, 3, v_l_1533_);
lean_ctor_set(v___x_1684_, 2, v_v_1803_);
lean_ctor_set(v___x_1684_, 1, v_k_1802_);
lean_ctor_set(v___x_1684_, 0, v___x_1540_);
v___x_1813_ = v___x_1684_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_k_1802_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_v_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_l_1533_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 4, v___x_1813_);
lean_ctor_set(v___x_1800_, 3, v___x_1811_);
lean_ctor_set(v___x_1800_, 2, v_v_1805_);
lean_ctor_set(v___x_1800_, 1, v_k_1804_);
lean_ctor_set(v___x_1800_, 0, v___x_1809_);
v___x_1815_ = v___x_1800_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_k_1804_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_v_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
else
{
lean_object* v_k_1829_; lean_object* v_v_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v_k_1829_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_k_1829_);
v_v_1830_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_v_1830_);
lean_dec_ref(v___x_1686_);
v___x_1831_ = lean_unsigned_to_nat(2u);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 4, v_r_1534_);
lean_ctor_set(v___x_1684_, 3, v_l_1350_);
lean_ctor_set(v___x_1684_, 2, v_v_1830_);
lean_ctor_set(v___x_1684_, 1, v_k_1829_);
lean_ctor_set(v___x_1684_, 0, v___x_1831_);
v___x_1833_ = v___x_1684_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_k_1829_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_v_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_r_1534_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
}
else
{
return v_l_1350_;
}
}
else
{
return v_r_1351_;
}
}
default: 
{
lean_object* v_impl_1841_; lean_object* v___x_1842_; 
v_impl_1841_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1346_, v_r_1351_);
v___x_1842_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1841_) == 0)
{
if (lean_obj_tag(v_l_1350_) == 0)
{
lean_object* v_size_1843_; lean_object* v_size_1844_; lean_object* v_k_1845_; lean_object* v_v_1846_; lean_object* v_l_1847_; lean_object* v_r_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_size_1843_ = lean_ctor_get(v_impl_1841_, 0);
lean_inc(v_size_1843_);
v_size_1844_ = lean_ctor_get(v_l_1350_, 0);
v_k_1845_ = lean_ctor_get(v_l_1350_, 1);
v_v_1846_ = lean_ctor_get(v_l_1350_, 2);
v_l_1847_ = lean_ctor_get(v_l_1350_, 3);
v_r_1848_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1848_);
v___x_1849_ = lean_unsigned_to_nat(3u);
v___x_1850_ = lean_nat_mul(v___x_1849_, v_size_1843_);
v___x_1851_ = lean_nat_dec_lt(v___x_1850_, v_size_1844_);
lean_dec(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec(v_r_1848_);
v___x_1852_ = lean_nat_add(v___x_1842_, v_size_1844_);
v___x_1853_ = lean_nat_add(v___x_1852_, v_size_1843_);
lean_dec(v_size_1843_);
lean_dec(v___x_1852_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_impl_1841_);
lean_ctor_set(v___x_1353_, 0, v___x_1853_);
v___x_1855_ = v___x_1353_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_impl_1841_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1922_; 
lean_inc(v_l_1847_);
lean_inc(v_v_1846_);
lean_inc(v_k_1845_);
lean_inc(v_size_1844_);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1923_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_l_1350_, 2);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1350_, 1);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1927_);
v___x_1858_ = v_l_1350_;
v_isShared_1859_ = v_isSharedCheck_1922_;
goto v_resetjp_1857_;
}
else
{
lean_dec(v_l_1350_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1922_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_size_1860_; lean_object* v_size_1861_; lean_object* v_k_1862_; lean_object* v_v_1863_; lean_object* v_l_1864_; lean_object* v_r_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_size_1860_ = lean_ctor_get(v_l_1847_, 0);
v_size_1861_ = lean_ctor_get(v_r_1848_, 0);
v_k_1862_ = lean_ctor_get(v_r_1848_, 1);
v_v_1863_ = lean_ctor_get(v_r_1848_, 2);
v_l_1864_ = lean_ctor_get(v_r_1848_, 3);
v_r_1865_ = lean_ctor_get(v_r_1848_, 4);
v___x_1866_ = lean_unsigned_to_nat(2u);
v___x_1867_ = lean_nat_mul(v___x_1866_, v_size_1860_);
v___x_1868_ = lean_nat_dec_lt(v_size_1861_, v___x_1867_);
lean_dec(v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1897_; 
lean_inc(v_r_1865_);
lean_inc(v_l_1864_);
lean_inc(v_v_1863_);
lean_inc(v_k_1862_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_r_1848_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1898_ = lean_ctor_get(v_r_1848_, 4);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_r_1848_, 3);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_r_1848_, 2);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_r_1848_, 1);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_r_1848_, 0);
lean_dec(v_unused_1902_);
v___x_1870_ = v_r_1848_;
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v_r_1848_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1897_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___x_1885_; lean_object* v___y_1887_; 
v___x_1872_ = lean_nat_add(v___x_1842_, v_size_1844_);
lean_dec(v_size_1844_);
v___x_1873_ = lean_nat_add(v___x_1872_, v_size_1843_);
lean_dec(v___x_1872_);
v___x_1885_ = lean_nat_add(v___x_1842_, v_size_1860_);
if (lean_obj_tag(v_l_1864_) == 0)
{
lean_object* v_size_1895_; 
v_size_1895_ = lean_ctor_get(v_l_1864_, 0);
lean_inc(v_size_1895_);
v___y_1887_ = v_size_1895_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_unsigned_to_nat(0u);
v___y_1887_ = v___x_1896_;
goto v___jp_1886_;
}
v___jp_1874_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_nat_add(v___y_1875_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec(v___y_1875_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 4, v_impl_1841_);
lean_ctor_set(v___x_1870_, 3, v_r_1865_);
lean_ctor_set(v___x_1870_, 2, v_v_1349_);
lean_ctor_set(v___x_1870_, 1, v_k_1348_);
lean_ctor_set(v___x_1870_, 0, v___x_1878_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_r_1865_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_impl_1841_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 4, v___x_1880_);
lean_ctor_set(v___x_1858_, 3, v___y_1876_);
lean_ctor_set(v___x_1858_, 2, v_v_1863_);
lean_ctor_set(v___x_1858_, 1, v_k_1862_);
lean_ctor_set(v___x_1858_, 0, v___x_1873_);
v___x_1882_ = v___x_1858_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_k_1862_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1863_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v___y_1876_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
v___jp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_nat_add(v___x_1885_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec(v___x_1885_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1864_);
lean_ctor_set(v___x_1353_, 3, v_l_1847_);
lean_ctor_set(v___x_1353_, 2, v_v_1846_);
lean_ctor_set(v___x_1353_, 1, v_k_1845_);
lean_ctor_set(v___x_1353_, 0, v___x_1888_);
v___x_1890_ = v___x_1353_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1845_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1846_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_l_1864_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_nat_add(v___x_1842_, v_size_1843_);
lean_dec(v_size_1843_);
if (lean_obj_tag(v_r_1865_) == 0)
{
lean_object* v_size_1892_; 
v_size_1892_ = lean_ctor_get(v_r_1865_, 0);
lean_inc(v_size_1892_);
v___y_1875_ = v___x_1891_;
v___y_1876_ = v___x_1890_;
v___y_1877_ = v_size_1892_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_unsigned_to_nat(0u);
v___y_1875_ = v___x_1891_;
v___y_1876_ = v___x_1890_;
v___y_1877_ = v___x_1893_;
goto v___jp_1874_;
}
}
}
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_del_object(v___x_1353_);
v___x_1903_ = lean_nat_add(v___x_1842_, v_size_1844_);
lean_dec(v_size_1844_);
v___x_1904_ = lean_nat_add(v___x_1903_, v_size_1843_);
lean_dec(v___x_1903_);
v___x_1905_ = lean_nat_add(v___x_1842_, v_size_1843_);
lean_dec(v_size_1843_);
v___x_1906_ = lean_nat_add(v___x_1905_, v_size_1861_);
lean_dec(v___x_1905_);
lean_inc_ref(v_impl_1841_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 4, v_impl_1841_);
lean_ctor_set(v___x_1858_, 3, v_r_1848_);
lean_ctor_set(v___x_1858_, 2, v_v_1349_);
lean_ctor_set(v___x_1858_, 1, v_k_1348_);
lean_ctor_set(v___x_1858_, 0, v___x_1906_);
v___x_1908_ = v___x_1858_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_r_1848_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_impl_1841_);
v___x_1908_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_isSharedCheck_1915_ = !lean_is_exclusive(v_impl_1841_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; 
v_unused_1916_ = lean_ctor_get(v_impl_1841_, 4);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_impl_1841_, 3);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_impl_1841_, 2);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_impl_1841_, 1);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_impl_1841_, 0);
lean_dec(v_unused_1920_);
v___x_1910_ = v_impl_1841_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v_impl_1841_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v___x_1908_);
lean_ctor_set(v___x_1910_, 3, v_l_1847_);
lean_ctor_set(v___x_1910_, 2, v_v_1846_);
lean_ctor_set(v___x_1910_, 1, v_k_1845_);
lean_ctor_set(v___x_1910_, 0, v___x_1904_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1845_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1846_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v___x_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v_size_1928_ = lean_ctor_get(v_impl_1841_, 0);
lean_inc(v_size_1928_);
v___x_1929_ = lean_nat_add(v___x_1842_, v_size_1928_);
lean_dec(v_size_1928_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_impl_1841_);
lean_ctor_set(v___x_1353_, 0, v___x_1929_);
v___x_1931_ = v___x_1353_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_impl_1841_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
if (lean_obj_tag(v_l_1350_) == 0)
{
lean_object* v_l_1933_; 
v_l_1933_ = lean_ctor_get(v_l_1350_, 3);
if (lean_obj_tag(v_l_1933_) == 0)
{
lean_object* v_r_1934_; 
lean_inc_ref(v_l_1933_);
v_r_1934_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1934_);
if (lean_obj_tag(v_r_1934_) == 0)
{
lean_object* v_size_1935_; lean_object* v_k_1936_; lean_object* v_v_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1950_; 
v_size_1935_ = lean_ctor_get(v_l_1350_, 0);
v_k_1936_ = lean_ctor_get(v_l_1350_, 1);
v_v_1937_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1951_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1952_);
v___x_1939_ = v_l_1350_;
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_v_1937_);
lean_inc(v_k_1936_);
lean_inc(v_size_1935_);
lean_dec(v_l_1350_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_size_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v_size_1941_ = lean_ctor_get(v_r_1934_, 0);
v___x_1942_ = lean_nat_add(v___x_1842_, v_size_1935_);
lean_dec(v_size_1935_);
v___x_1943_ = lean_nat_add(v___x_1842_, v_size_1941_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_impl_1841_);
lean_ctor_set(v___x_1939_, 3, v_r_1934_);
lean_ctor_set(v___x_1939_, 2, v_v_1349_);
lean_ctor_set(v___x_1939_, 1, v_k_1348_);
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_r_1934_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_impl_1841_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1945_);
lean_ctor_set(v___x_1353_, 3, v_l_1933_);
lean_ctor_set(v___x_1353_, 2, v_v_1937_);
lean_ctor_set(v___x_1353_, 1, v_k_1936_);
lean_ctor_set(v___x_1353_, 0, v___x_1942_);
v___x_1947_ = v___x_1353_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1937_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_k_1953_; lean_object* v_v_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1965_; 
v_k_1953_ = lean_ctor_get(v_l_1350_, 1);
v_v_1954_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; 
v_unused_1966_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1968_);
v___x_1956_ = v_l_1350_;
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_v_1954_);
lean_inc(v_k_1953_);
lean_dec(v_l_1350_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_unsigned_to_nat(3u);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 3, v_r_1934_);
lean_ctor_set(v___x_1956_, 2, v_v_1349_);
lean_ctor_set(v___x_1956_, 1, v_k_1348_);
lean_ctor_set(v___x_1956_, 0, v___x_1842_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_r_1934_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_r_1934_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1960_);
lean_ctor_set(v___x_1353_, 3, v_l_1933_);
lean_ctor_set(v___x_1353_, 2, v_v_1954_);
lean_ctor_set(v___x_1353_, 1, v_k_1953_);
lean_ctor_set(v___x_1353_, 0, v___x_1958_);
v___x_1962_ = v___x_1353_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
else
{
lean_object* v_r_1969_; 
v_r_1969_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1969_);
if (lean_obj_tag(v_r_1969_) == 0)
{
lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1994_; 
lean_inc(v_l_1933_);
v_k_1970_ = lean_ctor_get(v_l_1350_, 1);
v_v_1971_ = lean_ctor_get(v_l_1350_, 2);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_l_1350_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1995_ = lean_ctor_get(v_l_1350_, 4);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_l_1350_, 3);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_l_1350_, 0);
lean_dec(v_unused_1997_);
v___x_1973_ = v_l_1350_;
v_isShared_1974_ = v_isSharedCheck_1994_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
lean_dec(v_l_1350_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1994_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1990_; 
v_k_1975_ = lean_ctor_get(v_r_1969_, 1);
v_v_1976_ = lean_ctor_get(v_r_1969_, 2);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_r_1969_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; lean_object* v_unused_1993_; 
v_unused_1991_ = lean_ctor_get(v_r_1969_, 4);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_r_1969_, 3);
lean_dec(v_unused_1992_);
v_unused_1993_ = lean_ctor_get(v_r_1969_, 0);
lean_dec(v_unused_1993_);
v___x_1978_ = v_r_1969_;
v_isShared_1979_ = v_isSharedCheck_1990_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
lean_dec(v_r_1969_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1990_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_unsigned_to_nat(3u);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v_l_1933_);
lean_ctor_set(v___x_1978_, 3, v_l_1933_);
lean_ctor_set(v___x_1978_, 2, v_v_1971_);
lean_ctor_set(v___x_1978_, 1, v_k_1970_);
lean_ctor_set(v___x_1978_, 0, v___x_1842_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_l_1933_);
v___x_1982_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v_l_1933_);
lean_ctor_set(v___x_1973_, 2, v_v_1349_);
lean_ctor_set(v___x_1973_, 1, v_k_1348_);
lean_ctor_set(v___x_1973_, 0, v___x_1842_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_l_1933_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_l_1933_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v___x_1984_);
lean_ctor_set(v___x_1353_, 3, v___x_1982_);
lean_ctor_set(v___x_1353_, 2, v_v_1976_);
lean_ctor_set(v___x_1353_, 1, v_k_1975_);
lean_ctor_set(v___x_1353_, 0, v___x_1980_);
v___x_1986_ = v___x_1353_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_unsigned_to_nat(2u);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_r_1969_);
lean_ctor_set(v___x_1353_, 0, v___x_1998_);
v___x_2000_ = v___x_1353_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1969_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2003_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 4, v_l_1350_);
lean_ctor_set(v___x_1353_, 0, v___x_1842_);
v___x_2003_ = v___x_1353_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_l_1350_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_l_1350_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
else
{
return v_t_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2007_, lean_object* v_t_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2007_, v_t_2008_);
lean_dec(v_k_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2010_, lean_object* v_v_2011_, lean_object* v_i_2012_){
_start:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = lean_array_get_size(v_xs_2010_);
v___x_2014_ = lean_nat_dec_lt(v_i_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_i_2012_);
v___x_2015_ = lean_box(0);
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = lean_array_fget_borrowed(v_xs_2010_, v_i_2012_);
v___x_2017_ = l_Lean_instBEqFVarId_beq(v___x_2016_, v_v_2011_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_add(v_i_2012_, v___x_2018_);
lean_dec(v_i_2012_);
v_i_2012_ = v___x_2019_;
goto _start;
}
else
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_i_2012_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2022_, lean_object* v_v_2023_, lean_object* v_i_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2022_, v_v_2023_, v_i_2024_);
lean_dec(v_v_2023_);
lean_dec_ref(v_xs_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2026_, lean_object* v_v_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2026_, v_v_2027_, v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2030_, lean_object* v_v_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2030_, v_v_2031_);
lean_dec(v_v_2031_);
lean_dec_ref(v_xs_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2033_, size_t v_x_2034_, lean_object* v_x_2035_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v_es_2036_; lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v_j_2040_; lean_object* v_entry_2041_; 
v_es_2036_ = lean_ctor_get(v_x_2033_, 0);
v___x_2037_ = lean_box(2);
v___x_2038_ = ((size_t)31ULL);
v___x_2039_ = lean_usize_land(v_x_2034_, v___x_2038_);
v_j_2040_ = lean_usize_to_nat(v___x_2039_);
v_entry_2041_ = lean_array_get(v___x_2037_, v_es_2036_, v_j_2040_);
switch(lean_obj_tag(v_entry_2041_))
{
case 0:
{
lean_object* v_key_2042_; uint8_t v___x_2043_; 
v_key_2042_ = lean_ctor_get(v_entry_2041_, 0);
lean_inc(v_key_2042_);
lean_dec_ref_known(v_entry_2041_, 2);
v___x_2043_ = l_Lean_instBEqFVarId_beq(v_x_2035_, v_key_2042_);
lean_dec(v_key_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v_j_2040_);
return v_x_2033_;
}
else
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_inc_ref(v_es_2036_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_x_2033_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v_x_2033_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v_x_2033_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_array_set(v_es_2036_, v_j_2040_, v___x_2037_);
lean_dec(v_j_2040_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
case 1:
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2087_; 
lean_inc_ref(v_es_2036_);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_x_2033_, 0);
lean_dec(v_unused_2088_);
v___x_2054_ = v_x_2033_;
v_isShared_2055_ = v_isSharedCheck_2087_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v_x_2033_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2087_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_node_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2086_; 
v_node_2056_ = lean_ctor_get(v_entry_2041_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_entry_2041_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2058_ = v_entry_2041_;
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_node_2056_);
lean_dec(v_entry_2041_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2086_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
size_t v___x_2060_; lean_object* v_entries_2061_; size_t v___x_2062_; lean_object* v_newNode_2063_; lean_object* v___x_2064_; 
v___x_2060_ = ((size_t)5ULL);
v_entries_2061_ = lean_array_set(v_es_2036_, v_j_2040_, v___x_2037_);
v___x_2062_ = lean_usize_shift_right(v_x_2034_, v___x_2060_);
v_newNode_2063_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2056_, v___x_2062_, v_x_2035_);
lean_inc_ref(v_newNode_2063_);
v___x_2064_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_newNode_2063_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_newNode_2063_);
v___x_2066_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_array_set(v_entries_2061_, v_j_2040_, v___x_2066_);
lean_dec(v_j_2040_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2067_);
v___x_2069_ = v___x_2054_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_val_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_newNode_2063_);
lean_del_object(v___x_2058_);
v_val_2072_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v___x_2064_, 1);
v_fst_2073_ = lean_ctor_get(v_val_2072_, 0);
v_snd_2074_ = lean_ctor_get(v_val_2072_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_val_2072_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2076_ = v_val_2072_;
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2073_);
lean_dec(v_val_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_fst_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_snd_2074_);
v___x_2079_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_array_set(v_entries_2061_, v_j_2040_, v___x_2079_);
lean_dec(v_j_2040_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2080_);
v___x_2082_ = v___x_2054_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2040_);
return v_x_2033_;
}
}
}
else
{
lean_object* v_ks_2089_; lean_object* v_vs_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_ks_2089_ = lean_ctor_get(v_x_2033_, 0);
v_vs_2090_ = lean_ctor_get(v_x_2033_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v_x_2033_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_vs_2090_);
lean_inc(v_ks_2089_);
lean_dec(v_x_2033_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2089_, v_x_2035_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2096_; 
if (v_isShared_2093_ == 0)
{
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_ks_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_vs_2090_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_object* v_val_2098_; lean_object* v_keys_x27_2099_; lean_object* v_vals_x27_2100_; lean_object* v___x_2102_; 
v_val_2098_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_val_2098_, 2);
lean_dec_ref_known(v___x_2094_, 1);
v_keys_x27_2099_ = l_Array_eraseIdx___redArg(v_ks_2089_, v_val_2098_);
v_vals_x27_2100_ = l_Array_eraseIdx___redArg(v_vs_2090_, v_val_2098_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v_vals_x27_2100_);
lean_ctor_set(v___x_2092_, 0, v_keys_x27_2099_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_keys_x27_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_vals_x27_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
size_t v_x_2640__boxed_2108_; lean_object* v_res_2109_; 
v_x_2640__boxed_2108_ = lean_unbox_usize(v_x_2106_);
lean_dec(v_x_2106_);
v_res_2109_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2105_, v_x_2640__boxed_2108_, v_x_2107_);
lean_dec(v_x_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
uint64_t v___x_2112_; size_t v_h_2113_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_instHashableFVarId_hash(v_x_2111_);
v_h_2113_ = lean_uint64_to_usize(v___x_2112_);
v___x_2114_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2110_, v_h_2113_, v_x_2111_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2115_, v_x_2116_);
lean_dec(v_x_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase(lean_object* v_lctx_2118_, lean_object* v_fvarId_2119_){
_start:
{
lean_object* v_fvarIdToDecl_2120_; lean_object* v_decls_2121_; lean_object* v_auxDeclToFullName_2122_; lean_object* v___x_2123_; 
v_fvarIdToDecl_2120_ = lean_ctor_get(v_lctx_2118_, 0);
v_decls_2121_ = lean_ctor_get(v_lctx_2118_, 1);
v_auxDeclToFullName_2122_ = lean_ctor_get(v_lctx_2118_, 2);
v___x_2123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2120_, v_fvarId_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
return v_lctx_2118_;
}
else
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2143_; 
lean_inc(v_auxDeclToFullName_2122_);
lean_inc_ref(v_decls_2121_);
lean_inc_ref(v_fvarIdToDecl_2120_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_lctx_2118_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2144_ = lean_ctor_get(v_lctx_2118_, 2);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_lctx_2118_, 1);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_lctx_2118_, 0);
lean_dec(v_unused_2146_);
v___x_2125_ = v_lctx_2118_;
v_isShared_2126_ = v_isSharedCheck_2143_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_lctx_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2143_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_val_2127_; lean_object* v___x_2128_; lean_object* v___y_2130_; lean_object* v_index_2142_; 
v_val_2127_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2128_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2120_, v_fvarId_2119_);
v_index_2142_ = lean_ctor_get(v_val_2127_, 0);
lean_inc(v_index_2142_);
v___y_2130_ = v_index_2142_;
goto v___jp_2129_;
v___jp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Lean_PersistentArray_set___redArg(v_decls_2121_, v___y_2130_, v___x_2131_);
lean_dec(v___y_2130_);
v___x_2133_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2132_);
v___x_2134_ = l_Lean_LocalDecl_isAuxDecl(v_val_2127_);
lean_dec(v_val_2127_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2136_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v___x_2133_);
lean_ctor_set(v___x_2125_, 0, v___x_2128_);
v___x_2136_ = v___x_2125_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_auxDeclToFullName_2122_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2119_, v_auxDeclToFullName_2122_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___x_2138_);
lean_ctor_set(v___x_2125_, 1, v___x_2133_);
lean_ctor_set(v___x_2125_, 0, v___x_2128_);
v___x_2140_ = v___x_2125_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_erase___boxed(lean_object* v_lctx_2147_, lean_object* v_fvarId_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_LocalContext_erase(v_lctx_2147_, v_fvarId_2148_);
lean_dec(v_fvarId_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2154_, v_x_2155_, v_x_2156_);
lean_dec(v_x_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2158_, lean_object* v_k_2159_, lean_object* v_t_2160_, lean_object* v_h_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2159_, v_t_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2163_, lean_object* v_k_2164_, lean_object* v_t_2165_, lean_object* v_h_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2163_, v_k_2164_, v_t_2165_, v_h_2166_);
lean_dec(v_k_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, size_t v_x_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2169_, v_x_2170_, v_x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
size_t v_x_2862__boxed_2177_; lean_object* v_res_2178_; 
v_x_2862__boxed_2177_ = lean_unbox_usize(v_x_2175_);
lean_dec(v_x_2175_);
v_res_2178_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2173_, v_x_2174_, v_x_2862__boxed_2177_, v_x_2176_);
lean_dec(v_x_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2179_){
_start:
{
lean_object* v_decls_2180_; lean_object* v_fvarIdToDecl_2181_; lean_object* v_auxDeclToFullName_2182_; lean_object* v_size_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_decls_2180_ = lean_ctor_get(v_lctx_2179_, 1);
v_fvarIdToDecl_2181_ = lean_ctor_get(v_lctx_2179_, 0);
v_auxDeclToFullName_2182_ = lean_ctor_get(v_lctx_2179_, 2);
v_size_2183_ = lean_ctor_get(v_decls_2180_, 2);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_nat_dec_eq(v_size_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_nat_sub(v_size_2183_, v___x_2187_);
v___x_2189_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2186_, v_decls_2180_, v___x_2188_);
lean_dec(v___x_2188_);
if (lean_obj_tag(v___x_2189_) == 0)
{
return v_lctx_2179_;
}
else
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2208_; 
lean_inc(v_auxDeclToFullName_2182_);
lean_inc_ref(v_fvarIdToDecl_2181_);
lean_inc_ref(v_decls_2180_);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_lctx_2179_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2209_ = lean_ctor_get(v_lctx_2179_, 2);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_lctx_2179_, 1);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_lctx_2179_, 0);
lean_dec(v_unused_2211_);
v___x_2191_ = v_lctx_2179_;
v_isShared_2192_ = v_isSharedCheck_2208_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v_lctx_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2208_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v_val_2193_; lean_object* v___y_2195_; lean_object* v_fvarId_2207_; 
v_val_2193_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v___x_2189_, 1);
v_fvarId_2207_ = lean_ctor_get(v_val_2193_, 1);
lean_inc(v_fvarId_2207_);
v___y_2195_ = v_fvarId_2207_;
goto v___jp_2194_;
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2196_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2181_, v___y_2195_);
v___x_2197_ = l_Lean_PersistentArray_pop___redArg(v_decls_2180_);
v___x_2198_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2197_);
v___x_2199_ = l_Lean_LocalDecl_isAuxDecl(v_val_2193_);
lean_dec(v_val_2193_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v___y_2195_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v___x_2198_);
lean_ctor_set(v___x_2191_, 0, v___x_2196_);
v___x_2201_ = v___x_2191_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_auxDeclToFullName_2182_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2195_, v_auxDeclToFullName_2182_);
lean_dec(v___y_2195_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 2, v___x_2203_);
lean_ctor_set(v___x_2191_, 1, v___x_2198_);
lean_ctor_set(v___x_2191_, 0, v___x_2196_);
v___x_2205_ = v___x_2191_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
else
{
return v_lctx_2179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2212_, lean_object* v_as_2213_, lean_object* v_i_2214_){
_start:
{
lean_object* v_zero_2215_; uint8_t v_isZero_2216_; 
v_zero_2215_ = lean_unsigned_to_nat(0u);
v_isZero_2216_ = lean_nat_dec_eq(v_i_2214_, v_zero_2215_);
if (v_isZero_2216_ == 1)
{
lean_object* v___x_2217_; 
lean_dec(v_i_2214_);
v___x_2217_ = lean_box(0);
return v___x_2217_;
}
else
{
lean_object* v_one_2218_; lean_object* v_n_2219_; lean_object* v___y_2221_; lean_object* v___x_2223_; lean_object* v___y_2225_; 
v_one_2218_ = lean_unsigned_to_nat(1u);
v_n_2219_ = lean_nat_sub(v_i_2214_, v_one_2218_);
lean_dec(v_i_2214_);
v___x_2223_ = lean_array_fget_borrowed(v_as_2213_, v_n_2219_);
if (lean_obj_tag(v___x_2223_) == 0)
{
v___y_2221_ = v___x_2223_;
goto v___jp_2220_;
}
else
{
lean_object* v_val_2228_; lean_object* v_userName_2229_; 
v_val_2228_ = lean_ctor_get(v___x_2223_, 0);
v_userName_2229_ = lean_ctor_get(v_val_2228_, 2);
v___y_2225_ = v_userName_2229_;
goto v___jp_2224_;
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
v_i_2214_ = v_n_2219_;
goto _start;
}
else
{
lean_dec(v_n_2219_);
lean_inc_ref(v___y_2221_);
return v___y_2221_;
}
}
v___jp_2224_:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_name_eq(v___y_2225_, v_userName_2212_);
if (v___x_2226_ == 0)
{
v_i_2214_ = v_n_2219_;
goto _start;
}
else
{
v___y_2221_ = v___x_2223_;
goto v___jp_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2230_, lean_object* v_as_2231_, lean_object* v_i_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2230_, v_as_2231_, v_i_2232_);
lean_dec_ref(v_as_2231_);
lean_dec(v_userName_2230_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2234_, lean_object* v_as_2235_, lean_object* v_i_2236_){
_start:
{
lean_object* v_zero_2237_; uint8_t v_isZero_2238_; 
v_zero_2237_ = lean_unsigned_to_nat(0u);
v_isZero_2238_ = lean_nat_dec_eq(v_i_2236_, v_zero_2237_);
if (v_isZero_2238_ == 1)
{
lean_object* v___x_2239_; 
lean_dec(v_i_2236_);
v___x_2239_ = lean_box(0);
return v___x_2239_;
}
else
{
lean_object* v_one_2240_; lean_object* v_n_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_one_2240_ = lean_unsigned_to_nat(1u);
v_n_2241_ = lean_nat_sub(v_i_2236_, v_one_2240_);
lean_dec(v_i_2236_);
v___x_2242_ = lean_array_fget_borrowed(v_as_2235_, v_n_2241_);
v___x_2243_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2234_, v___x_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
v_i_2236_ = v_n_2241_;
goto _start;
}
else
{
lean_dec(v_n_2241_);
return v___x_2243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
lean_object* v_cs_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_cs_2247_ = lean_ctor_get(v_x_2246_, 0);
v___x_2248_ = lean_array_get_size(v_cs_2247_);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2245_, v_cs_2247_, v___x_2248_);
return v___x_2249_;
}
else
{
lean_object* v_vs_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_vs_2250_ = lean_ctor_get(v_x_2246_, 0);
v___x_2251_ = lean_array_get_size(v_vs_2250_);
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2245_, v_vs_2250_, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2253_, v_x_2254_);
lean_dec_ref(v_x_2254_);
lean_dec(v_userName_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2256_, lean_object* v_as_2257_, lean_object* v_i_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2256_, v_as_2257_, v_i_2258_);
lean_dec_ref(v_as_2257_);
lean_dec(v_userName_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2260_, lean_object* v_t_2261_){
_start:
{
lean_object* v_root_2262_; lean_object* v_tail_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_root_2262_ = lean_ctor_get(v_t_2261_, 0);
v_tail_2263_ = lean_ctor_get(v_t_2261_, 1);
v___x_2264_ = lean_array_get_size(v_tail_2263_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2260_, v_tail_2263_, v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2260_, v_root_2262_);
return v___x_2266_;
}
else
{
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2267_, lean_object* v_t_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2267_, v_t_2268_);
lean_dec_ref(v_t_2268_);
lean_dec(v_userName_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2270_, lean_object* v_userName_2271_){
_start:
{
lean_object* v_decls_2272_; lean_object* v___x_2273_; 
v_decls_2272_ = lean_ctor_get(v_lctx_2270_, 1);
v___x_2273_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2271_, v_decls_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2274_, lean_object* v_userName_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2274_, v_userName_2275_);
lean_dec(v_userName_2275_);
lean_dec_ref(v_lctx_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2277_, lean_object* v_as_2278_, lean_object* v_i_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2277_, v_as_2278_, v_i_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2282_, lean_object* v_as_2283_, lean_object* v_i_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2282_, v_as_2283_, v_i_2284_, v_a_2285_);
lean_dec_ref(v_as_2283_);
lean_dec(v_userName_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2287_, lean_object* v_as_2288_, lean_object* v_i_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2287_, v_as_2288_, v_i_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2292_, lean_object* v_as_2293_, lean_object* v_i_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2292_, v_as_2293_, v_i_2294_, v_a_2295_);
lean_dec_ref(v_as_2293_);
lean_dec(v_userName_2292_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2300_, lean_object* v_userName_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2300_, v_userName_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2303_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2304_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2305_ = lean_unsigned_to_nat(401u);
v___x_2306_ = lean_unsigned_to_nat(17u);
v___x_2307_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2308_ = 1;
v___x_2309_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2301_, v___x_2308_);
v___x_2310_ = lean_string_append(v___x_2307_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
v___x_2313_ = l_mkPanicMessageWithDecl(v___x_2303_, v___x_2304_, v___x_2305_, v___x_2306_, v___x_2312_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v_val_2315_; 
lean_dec(v_userName_2301_);
v_val_2315_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2315_);
lean_dec_ref_known(v___x_2302_, 1);
return v_val_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2316_, lean_object* v_userName_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2316_, v_userName_2317_);
lean_dec_ref(v_lctx_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2319_, lean_object* v_userName_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2319_, v_userName_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
uint8_t v___x_2322_; 
v___x_2322_ = 0;
return v___x_2322_;
}
else
{
uint8_t v___x_2323_; 
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = 1;
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2324_, lean_object* v_userName_2325_){
_start:
{
uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_res_2326_ = l_Lean_LocalContext_usesUserName(v_lctx_2324_, v_userName_2325_);
lean_dec(v_userName_2325_);
lean_dec_ref(v_lctx_2324_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2328_, lean_object* v_suggestion_2329_, lean_object* v_i_2330_){
_start:
{
lean_object* v_curr_2331_; uint8_t v___x_2332_; 
lean_inc(v_i_2330_);
lean_inc(v_suggestion_2329_);
v_curr_2331_ = lean_name_append_index_after(v_suggestion_2329_, v_i_2330_);
v___x_2332_ = l_Lean_LocalContext_usesUserName(v_lctx_2328_, v_curr_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v_suggestion_2329_);
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_add(v_i_2330_, v___x_2333_);
lean_dec(v_i_2330_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_curr_2331_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
return v___x_2335_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_curr_2331_);
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_i_2330_, v___x_2336_);
lean_dec(v_i_2330_);
v_i_2330_ = v___x_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2339_, lean_object* v_suggestion_2340_, lean_object* v_i_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2339_, v_suggestion_2340_, v_i_2341_);
lean_dec_ref(v_lctx_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2343_, lean_object* v_suggestion_2344_){
_start:
{
lean_object* v_suggestion_2345_; uint8_t v___x_2346_; 
v_suggestion_2345_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2344_);
v___x_2346_ = l_Lean_LocalContext_usesUserName(v_lctx_2343_, v_suggestion_2345_);
if (v___x_2346_ == 0)
{
return v_suggestion_2345_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_fst_2349_; 
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2343_, v_suggestion_2345_, v___x_2347_);
v_fst_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_fst_2349_);
lean_dec_ref(v___x_2348_);
return v_fst_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2350_, lean_object* v_suggestion_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_LocalContext_getUnusedName(v_lctx_2350_, v_suggestion_2351_);
lean_dec(v_suggestion_2351_);
lean_dec_ref(v_lctx_2350_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2353_){
_start:
{
lean_object* v_decls_2354_; lean_object* v_size_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_decls_2354_ = lean_ctor_get(v_lctx_2353_, 1);
v_size_2355_ = lean_ctor_get(v_decls_2354_, 2);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_sub(v_size_2355_, v___x_2357_);
v___x_2359_ = lean_nat_dec_lt(v___x_2358_, v_size_2355_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_dec(v___x_2358_);
v___x_2360_ = l_outOfBounds___redArg(v___x_2356_);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2356_, v_decls_2354_, v___x_2358_);
lean_dec(v___x_2358_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_LocalContext_lastDecl(v_lctx_2362_);
lean_dec_ref(v_lctx_2362_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2364_, lean_object* v_fvarId_2365_, lean_object* v_userName_2366_){
_start:
{
lean_object* v_fvarIdToDecl_2367_; lean_object* v_decls_2368_; lean_object* v_auxDeclToFullName_2369_; lean_object* v_decl_2370_; lean_object* v_decl_2371_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2379_; lean_object* v_fvarId_2382_; 
v_fvarIdToDecl_2367_ = lean_ctor_get(v_lctx_2364_, 0);
lean_inc_ref(v_fvarIdToDecl_2367_);
v_decls_2368_ = lean_ctor_get(v_lctx_2364_, 1);
lean_inc_ref(v_decls_2368_);
v_auxDeclToFullName_2369_ = lean_ctor_get(v_lctx_2364_, 2);
lean_inc(v_auxDeclToFullName_2369_);
v_decl_2370_ = l_Lean_LocalContext_get_x21(v_lctx_2364_, v_fvarId_2365_);
v_decl_2371_ = l_Lean_LocalDecl_setUserName(v_decl_2370_, v_userName_2366_);
v_fvarId_2382_ = lean_ctor_get(v_decl_2371_, 1);
lean_inc(v_fvarId_2382_);
v___y_2379_ = v_fvarId_2382_;
goto v___jp_2378_;
v___jp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_decl_2371_);
v___x_2376_ = l_Lean_PersistentArray_set___redArg(v_decls_2368_, v___y_2374_, v___x_2375_);
lean_dec(v___y_2374_);
v___x_2377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2377_, 0, v___y_2373_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
lean_ctor_set(v___x_2377_, 2, v_auxDeclToFullName_2369_);
return v___x_2377_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v_index_2381_; 
lean_inc_ref(v_decl_2371_);
v___x_2380_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2367_, v___y_2379_, v_decl_2371_);
v_index_2381_ = lean_ctor_get(v_decl_2371_, 0);
lean_inc(v_index_2381_);
v___y_2373_ = v___x_2380_;
v___y_2374_ = v_index_2381_;
goto v___jp_2372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2383_, lean_object* v_fromName_2384_, lean_object* v_toName_2385_){
_start:
{
lean_object* v_fvarIdToDecl_2386_; lean_object* v_decls_2387_; lean_object* v_auxDeclToFullName_2388_; lean_object* v___x_2389_; 
v_fvarIdToDecl_2386_ = lean_ctor_get(v_lctx_2383_, 0);
v_decls_2387_ = lean_ctor_get(v_lctx_2383_, 1);
v_auxDeclToFullName_2388_ = lean_ctor_get(v_lctx_2383_, 2);
v___x_2389_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2383_, v_fromName_2384_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_dec(v_toName_2385_);
return v_lctx_2383_;
}
else
{
lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2414_; 
lean_inc(v_auxDeclToFullName_2388_);
lean_inc_ref(v_decls_2387_);
lean_inc_ref(v_fvarIdToDecl_2386_);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_lctx_2383_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2415_ = lean_ctor_get(v_lctx_2383_, 2);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_lctx_2383_, 1);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_lctx_2383_, 0);
lean_dec(v_unused_2417_);
v___x_2391_ = v_lctx_2383_;
v_isShared_2392_ = v_isSharedCheck_2414_;
goto v_resetjp_2390_;
}
else
{
lean_dec(v_lctx_2383_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2414_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_val_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2413_; 
v_val_2393_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2395_ = v___x_2389_;
v_isShared_2396_ = v_isSharedCheck_2413_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_val_2393_);
lean_dec(v___x_2389_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2413_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_decl_2397_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2409_; lean_object* v_fvarId_2412_; 
v_decl_2397_ = l_Lean_LocalDecl_setUserName(v_val_2393_, v_toName_2385_);
v_fvarId_2412_ = lean_ctor_get(v_decl_2397_, 1);
lean_inc(v_fvarId_2412_);
v___y_2409_ = v_fvarId_2412_;
goto v___jp_2408_;
v___jp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v_decl_2397_);
v___x_2402_ = v___x_2395_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_decl_2397_);
v___x_2402_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_PersistentArray_set___redArg(v_decls_2387_, v___y_2400_, v___x_2402_);
lean_dec(v___y_2400_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 1, v___x_2403_);
lean_ctor_set(v___x_2391_, 0, v___y_2399_);
v___x_2405_ = v___x_2391_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___y_2399_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_auxDeclToFullName_2388_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v_index_2411_; 
lean_inc_ref(v_decl_2397_);
v___x_2410_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2386_, v___y_2409_, v_decl_2397_);
v_index_2411_ = lean_ctor_get(v_decl_2397_, 0);
lean_inc(v_index_2411_);
v___y_2399_ = v___x_2410_;
v___y_2400_ = v_index_2411_;
goto v___jp_2398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2418_, lean_object* v_fromName_2419_, lean_object* v_toName_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_LocalContext_renameUserName(v_lctx_2418_, v_fromName_2419_, v_toName_2420_);
lean_dec(v_fromName_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2424_, lean_object* v_fvarId_2425_, lean_object* v_f_2426_){
_start:
{
lean_object* v_fvarIdToDecl_2427_; lean_object* v_decls_2428_; lean_object* v_auxDeclToFullName_2429_; lean_object* v___x_2430_; 
v_fvarIdToDecl_2427_ = lean_ctor_get(v_lctx_2424_, 0);
v_decls_2428_ = lean_ctor_get(v_lctx_2424_, 1);
v_auxDeclToFullName_2429_ = lean_ctor_get(v_lctx_2424_, 2);
lean_inc_ref(v_lctx_2424_);
v___x_2430_ = lean_local_ctx_find(v_lctx_2424_, v_fvarId_2425_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_dec_ref(v_f_2426_);
return v_lctx_2424_;
}
else
{
lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2457_; 
lean_inc(v_auxDeclToFullName_2429_);
lean_inc_ref(v_decls_2428_);
lean_inc_ref(v_fvarIdToDecl_2427_);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_lctx_2424_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; lean_object* v_unused_2459_; lean_object* v_unused_2460_; 
v_unused_2458_ = lean_ctor_get(v_lctx_2424_, 2);
lean_dec(v_unused_2458_);
v_unused_2459_ = lean_ctor_get(v_lctx_2424_, 1);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_lctx_2424_, 0);
lean_dec(v_unused_2460_);
v___x_2432_ = v_lctx_2424_;
v_isShared_2433_ = v_isSharedCheck_2457_;
goto v_resetjp_2431_;
}
else
{
lean_dec(v_lctx_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2457_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_val_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2456_; 
v_val_2434_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2436_ = v___x_2430_;
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_val_2434_);
lean_dec(v___x_2430_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_decl_2440_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2452_; lean_object* v_fvarId_2455_; 
v___x_2438_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2439_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2440_ = lean_apply_1(v_f_2426_, v_val_2434_);
v_fvarId_2455_ = lean_ctor_get(v_decl_2440_, 1);
lean_inc(v_fvarId_2455_);
v___y_2452_ = v_fvarId_2455_;
goto v___jp_2451_;
v___jp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v_decl_2440_);
v___x_2445_ = v___x_2436_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_decl_2440_);
v___x_2445_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = l_Lean_PersistentArray_set___redArg(v_decls_2428_, v___y_2443_, v___x_2445_);
lean_dec(v___y_2443_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2446_);
lean_ctor_set(v___x_2432_, 0, v___y_2442_);
v___x_2448_ = v___x_2432_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___y_2442_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_auxDeclToFullName_2429_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v_index_2454_; 
lean_inc_ref(v_decl_2440_);
v___x_2453_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2438_, v___x_2439_, v_fvarIdToDecl_2427_, v___y_2452_, v_decl_2440_);
v_index_2454_ = lean_ctor_get(v_decl_2440_, 0);
lean_inc(v_index_2454_);
v___y_2442_ = v___x_2453_;
v___y_2443_ = v_index_2454_;
goto v___jp_2441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2461_, lean_object* v_as_2462_, size_t v_i_2463_, size_t v_stop_2464_, lean_object* v_b_2465_){
_start:
{
lean_object* v___y_2467_; uint8_t v___x_2471_; 
v___x_2471_ = lean_usize_dec_eq(v_i_2463_, v_stop_2464_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_array_uget(v_as_2462_, v_i_2463_);
if (lean_obj_tag(v___x_2472_) == 0)
{
v___y_2467_ = v_b_2465_;
goto v___jp_2466_;
}
else
{
lean_object* v_val_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2500_; 
v_val_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2500_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_val_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2500_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_fvarIdToDecl_2477_; lean_object* v_decls_2478_; lean_object* v_auxDeclToFullName_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2499_; 
v_fvarIdToDecl_2477_ = lean_ctor_get(v_b_2465_, 0);
v_decls_2478_ = lean_ctor_get(v_b_2465_, 1);
v_auxDeclToFullName_2479_ = lean_ctor_get(v_b_2465_, 2);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_b_2465_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2481_ = v_b_2465_;
v_isShared_2482_ = v_isSharedCheck_2499_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_auxDeclToFullName_2479_);
lean_inc(v_decls_2478_);
lean_inc(v_fvarIdToDecl_2477_);
lean_dec(v_b_2465_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2499_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_decl_2483_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2495_; lean_object* v_fvarId_2498_; 
lean_inc_ref(v_f_2461_);
v_decl_2483_ = lean_apply_1(v_f_2461_, v_val_2473_);
v_fvarId_2498_ = lean_ctor_get(v_decl_2483_, 1);
lean_inc(v_fvarId_2498_);
v___y_2495_ = v_fvarId_2498_;
goto v___jp_2494_;
v___jp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v_decl_2483_);
v___x_2488_ = v___x_2475_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_decl_2483_);
v___x_2488_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = l_Lean_PersistentArray_set___redArg(v_decls_2478_, v___y_2486_, v___x_2488_);
lean_dec(v___y_2486_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2489_);
lean_ctor_set(v___x_2481_, 0, v___y_2485_);
v___x_2491_ = v___x_2481_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___y_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_auxDeclToFullName_2479_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
v___y_2467_ = v___x_2491_;
goto v___jp_2466_;
}
}
}
v___jp_2494_:
{
lean_object* v___x_2496_; lean_object* v_index_2497_; 
lean_inc_ref(v_decl_2483_);
v___x_2496_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2477_, v___y_2495_, v_decl_2483_);
v_index_2497_ = lean_ctor_get(v_decl_2483_, 0);
lean_inc(v_index_2497_);
v___y_2485_ = v___x_2496_;
v___y_2486_ = v_index_2497_;
goto v___jp_2484_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2461_);
return v_b_2465_;
}
v___jp_2466_:
{
size_t v___x_2468_; size_t v___x_2469_; 
v___x_2468_ = ((size_t)1ULL);
v___x_2469_ = lean_usize_add(v_i_2463_, v___x_2468_);
v_i_2463_ = v___x_2469_;
v_b_2465_ = v___y_2467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2501_, lean_object* v_as_2502_, lean_object* v_i_2503_, lean_object* v_stop_2504_, lean_object* v_b_2505_){
_start:
{
size_t v_i_boxed_2506_; size_t v_stop_boxed_2507_; lean_object* v_res_2508_; 
v_i_boxed_2506_ = lean_unbox_usize(v_i_2503_);
lean_dec(v_i_2503_);
v_stop_boxed_2507_ = lean_unbox_usize(v_stop_2504_);
lean_dec(v_stop_2504_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2501_, v_as_2502_, v_i_boxed_2506_, v_stop_boxed_2507_, v_b_2505_);
lean_dec_ref(v_as_2502_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_object* v_cs_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_cs_2512_ = lean_ctor_get(v_x_2510_, 0);
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = lean_array_get_size(v_cs_2512_);
v___x_2515_ = lean_nat_dec_lt(v___x_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v_f_2509_);
return v_x_2511_;
}
else
{
size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = lean_usize_of_nat(v___x_2514_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2509_, v_cs_2512_, v___x_2516_, v___x_2517_, v_x_2511_);
return v___x_2518_;
}
}
else
{
lean_object* v_vs_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_vs_2519_ = lean_ctor_get(v_x_2510_, 0);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_vs_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec_ref(v_f_2509_);
return v_x_2511_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2521_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2509_, v_vs_2519_, v___x_2523_, v___x_2524_, v_x_2511_);
return v___x_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2526_, lean_object* v_as_2527_, size_t v_i_2528_, size_t v_stop_2529_, lean_object* v_b_2530_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_eq(v_i_2528_, v_stop_2529_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; 
v___x_2532_ = lean_array_uget_borrowed(v_as_2527_, v_i_2528_);
lean_inc_ref(v_f_2526_);
v___x_2533_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2526_, v___x_2532_, v_b_2530_);
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2528_, v___x_2534_);
v_i_2528_ = v___x_2535_;
v_b_2530_ = v___x_2533_;
goto _start;
}
else
{
lean_dec_ref(v_f_2526_);
return v_b_2530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2537_, lean_object* v_as_2538_, lean_object* v_i_2539_, lean_object* v_stop_2540_, lean_object* v_b_2541_){
_start:
{
size_t v_i_boxed_2542_; size_t v_stop_boxed_2543_; lean_object* v_res_2544_; 
v_i_boxed_2542_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_stop_boxed_2543_ = lean_unbox_usize(v_stop_2540_);
lean_dec(v_stop_2540_);
v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2537_, v_as_2538_, v_i_boxed_2542_, v_stop_boxed_2543_, v_b_2541_);
lean_dec_ref(v_as_2538_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2545_, v_x_2546_, v_x_2547_);
lean_dec_ref(v_x_2546_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2549_, lean_object* v_x_2550_, size_t v_x_2551_, size_t v_x_2552_, lean_object* v_x_2553_){
_start:
{
if (lean_obj_tag(v_x_2550_) == 0)
{
lean_object* v_cs_2554_; lean_object* v___x_2555_; size_t v___x_2556_; lean_object* v_j_2557_; lean_object* v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_cs_2554_ = lean_ctor_get(v_x_2550_, 0);
v___x_2555_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2556_ = lean_usize_shift_right(v_x_2551_, v_x_2552_);
v_j_2557_ = lean_usize_to_nat(v___x_2556_);
v___x_2558_ = lean_array_get_borrowed(v___x_2555_, v_cs_2554_, v_j_2557_);
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_shift_left(v___x_2559_, v_x_2552_);
v___x_2561_ = lean_usize_sub(v___x_2560_, v___x_2559_);
v___x_2562_ = lean_usize_land(v_x_2551_, v___x_2561_);
v___x_2563_ = ((size_t)5ULL);
v___x_2564_ = lean_usize_sub(v_x_2552_, v___x_2563_);
lean_inc_ref(v_f_2549_);
v___x_2565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2549_, v___x_2558_, v___x_2562_, v___x_2564_, v_x_2553_);
v___x_2566_ = lean_unsigned_to_nat(1u);
v___x_2567_ = lean_nat_add(v_j_2557_, v___x_2566_);
lean_dec(v_j_2557_);
v___x_2568_ = lean_array_get_size(v_cs_2554_);
v___x_2569_ = lean_nat_dec_lt(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_dec(v___x_2567_);
lean_dec_ref(v_f_2549_);
return v___x_2565_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_usize_of_nat(v___x_2567_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_usize_of_nat(v___x_2568_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2549_, v_cs_2554_, v___x_2570_, v___x_2571_, v___x_2565_);
return v___x_2572_;
}
}
else
{
lean_object* v_vs_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_vs_2573_ = lean_ctor_get(v_x_2550_, 0);
v___x_2574_ = lean_usize_to_nat(v_x_2551_);
v___x_2575_ = lean_array_get_size(v_vs_2573_);
v___x_2576_ = lean_nat_dec_lt(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_dec(v___x_2574_);
lean_dec_ref(v_f_2549_);
return v_x_2553_;
}
else
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_usize_of_nat(v___x_2574_);
lean_dec(v___x_2574_);
v___x_2578_ = lean_usize_of_nat(v___x_2575_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2549_, v_vs_2573_, v___x_2577_, v___x_2578_, v_x_2553_);
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
size_t v_x_1489__boxed_2585_; size_t v_x_1490__boxed_2586_; lean_object* v_res_2587_; 
v_x_1489__boxed_2585_ = lean_unbox_usize(v_x_2582_);
lean_dec(v_x_2582_);
v_x_1490__boxed_2586_ = lean_unbox_usize(v_x_2583_);
lean_dec(v_x_2583_);
v_res_2587_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2580_, v_x_2581_, v_x_1489__boxed_2585_, v_x_1490__boxed_2586_, v_x_2584_);
lean_dec_ref(v_x_2581_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2588_, lean_object* v_t_2589_, lean_object* v_init_2590_, lean_object* v_start_2591_){
_start:
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_nat_dec_eq(v_start_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v_root_2594_; lean_object* v_tail_2595_; size_t v_shift_2596_; lean_object* v_tailOff_2597_; uint8_t v___x_2598_; 
v_root_2594_ = lean_ctor_get(v_t_2589_, 0);
v_tail_2595_ = lean_ctor_get(v_t_2589_, 1);
v_shift_2596_ = lean_ctor_get_usize(v_t_2589_, 4);
v_tailOff_2597_ = lean_ctor_get(v_t_2589_, 3);
v___x_2598_ = lean_nat_dec_le(v_tailOff_2597_, v_start_2591_);
if (v___x_2598_ == 0)
{
size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2599_ = lean_usize_of_nat(v_start_2591_);
lean_inc_ref(v_f_2588_);
v___x_2600_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2588_, v_root_2594_, v___x_2599_, v_shift_2596_, v_init_2590_);
v___x_2601_ = lean_array_get_size(v_tail_2595_);
v___x_2602_ = lean_nat_dec_lt(v___x_2592_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_dec_ref(v_f_2588_);
return v___x_2600_;
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2601_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2588_, v_tail_2595_, v___x_2603_, v___x_2604_, v___x_2600_);
return v___x_2605_;
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = lean_nat_sub(v_start_2591_, v_tailOff_2597_);
v___x_2607_ = lean_array_get_size(v_tail_2595_);
v___x_2608_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec(v___x_2606_);
lean_dec_ref(v_f_2588_);
return v_init_2590_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_usize_of_nat(v___x_2606_);
lean_dec(v___x_2606_);
v___x_2610_ = lean_usize_of_nat(v___x_2607_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2588_, v_tail_2595_, v___x_2609_, v___x_2610_, v_init_2590_);
return v___x_2611_;
}
}
}
else
{
lean_object* v_root_2612_; lean_object* v_tail_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_root_2612_ = lean_ctor_get(v_t_2589_, 0);
v_tail_2613_ = lean_ctor_get(v_t_2589_, 1);
lean_inc_ref(v_f_2588_);
v___x_2614_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2588_, v_root_2612_, v_init_2590_);
v___x_2615_ = lean_array_get_size(v_tail_2613_);
v___x_2616_ = lean_nat_dec_lt(v___x_2592_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_dec_ref(v_f_2588_);
return v___x_2614_;
}
else
{
size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = ((size_t)0ULL);
v___x_2618_ = lean_usize_of_nat(v___x_2615_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2588_, v_tail_2613_, v___x_2617_, v___x_2618_, v___x_2614_);
return v___x_2619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2620_, lean_object* v_t_2621_, lean_object* v_init_2622_, lean_object* v_start_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2620_, v_t_2621_, v_init_2622_, v_start_2623_);
lean_dec(v_start_2623_);
lean_dec_ref(v_t_2621_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2625_, lean_object* v_f_2626_){
_start:
{
lean_object* v_decls_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_decls_2627_ = lean_ctor_get(v_lctx_2625_, 1);
lean_inc_ref(v_decls_2627_);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2626_, v_decls_2627_, v_lctx_2625_, v___x_2628_);
lean_dec_ref(v_decls_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2630_, lean_object* v_fvarId_2631_, uint8_t v_kind_2632_){
_start:
{
lean_object* v_fvarIdToDecl_2633_; lean_object* v_decls_2634_; lean_object* v_auxDeclToFullName_2635_; lean_object* v___x_2636_; 
v_fvarIdToDecl_2633_ = lean_ctor_get(v_lctx_2630_, 0);
v_decls_2634_ = lean_ctor_get(v_lctx_2630_, 1);
v_auxDeclToFullName_2635_ = lean_ctor_get(v_lctx_2630_, 2);
lean_inc_ref(v_lctx_2630_);
v___x_2636_ = lean_local_ctx_find(v_lctx_2630_, v_fvarId_2631_);
if (lean_obj_tag(v___x_2636_) == 0)
{
return v_lctx_2630_;
}
else
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2661_; 
lean_inc(v_auxDeclToFullName_2635_);
lean_inc_ref(v_decls_2634_);
lean_inc_ref(v_fvarIdToDecl_2633_);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_lctx_2630_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; 
v_unused_2662_ = lean_ctor_get(v_lctx_2630_, 2);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_lctx_2630_, 1);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_lctx_2630_, 0);
lean_dec(v_unused_2664_);
v___x_2638_ = v_lctx_2630_;
v_isShared_2639_ = v_isSharedCheck_2661_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v_lctx_2630_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2661_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_val_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2660_; 
v_val_2640_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2642_ = v___x_2636_;
v_isShared_2643_ = v_isSharedCheck_2660_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_val_2640_);
lean_dec(v___x_2636_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2660_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_decl_2644_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2656_; lean_object* v_fvarId_2659_; 
v_decl_2644_ = l_Lean_LocalDecl_setKind(v_val_2640_, v_kind_2632_);
v_fvarId_2659_ = lean_ctor_get(v_decl_2644_, 1);
lean_inc(v_fvarId_2659_);
v___y_2656_ = v_fvarId_2659_;
goto v___jp_2655_;
v___jp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_decl_2644_);
v___x_2649_ = v___x_2642_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_decl_2644_);
v___x_2649_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = l_Lean_PersistentArray_set___redArg(v_decls_2634_, v___y_2647_, v___x_2649_);
lean_dec(v___y_2647_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___x_2650_);
lean_ctor_set(v___x_2638_, 0, v___y_2646_);
v___x_2652_ = v___x_2638_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___y_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_auxDeclToFullName_2635_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
v___jp_2655_:
{
lean_object* v___x_2657_; lean_object* v_index_2658_; 
lean_inc_ref(v_decl_2644_);
v___x_2657_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2633_, v___y_2656_, v_decl_2644_);
v_index_2658_ = lean_ctor_get(v_decl_2644_, 0);
lean_inc(v_index_2658_);
v___y_2646_ = v___x_2657_;
v___y_2647_ = v_index_2658_;
goto v___jp_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2665_, lean_object* v_fvarId_2666_, lean_object* v_kind_2667_){
_start:
{
uint8_t v_kind_boxed_2668_; lean_object* v_res_2669_; 
v_kind_boxed_2668_ = lean_unbox(v_kind_2667_);
v_res_2669_ = l_Lean_LocalContext_setKind(v_lctx_2665_, v_fvarId_2666_, v_kind_boxed_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2670_, lean_object* v_fvarId_2671_, uint8_t v_bi_2672_){
_start:
{
lean_object* v_fvarIdToDecl_2673_; lean_object* v_decls_2674_; lean_object* v_auxDeclToFullName_2675_; lean_object* v___x_2676_; 
v_fvarIdToDecl_2673_ = lean_ctor_get(v_lctx_2670_, 0);
v_decls_2674_ = lean_ctor_get(v_lctx_2670_, 1);
v_auxDeclToFullName_2675_ = lean_ctor_get(v_lctx_2670_, 2);
lean_inc_ref(v_lctx_2670_);
v___x_2676_ = lean_local_ctx_find(v_lctx_2670_, v_fvarId_2671_);
if (lean_obj_tag(v___x_2676_) == 0)
{
return v_lctx_2670_;
}
else
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_auxDeclToFullName_2675_);
lean_inc_ref(v_decls_2674_);
lean_inc_ref(v_fvarIdToDecl_2673_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_lctx_2670_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; 
v_unused_2702_ = lean_ctor_get(v_lctx_2670_, 2);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_lctx_2670_, 1);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_lctx_2670_, 0);
lean_dec(v_unused_2704_);
v___x_2678_ = v_lctx_2670_;
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v_lctx_2670_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_val_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2700_; 
v_val_2680_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2682_ = v___x_2676_;
v_isShared_2683_ = v_isSharedCheck_2700_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_val_2680_);
lean_dec(v___x_2676_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2700_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_decl_2684_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2696_; lean_object* v_fvarId_2699_; 
v_decl_2684_ = l_Lean_LocalDecl_setBinderInfo(v_val_2680_, v_bi_2672_);
v_fvarId_2699_ = lean_ctor_get(v_decl_2684_, 1);
lean_inc(v_fvarId_2699_);
v___y_2696_ = v_fvarId_2699_;
goto v___jp_2695_;
v___jp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v_decl_2684_);
v___x_2689_ = v___x_2682_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_decl_2684_);
v___x_2689_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = l_Lean_PersistentArray_set___redArg(v_decls_2674_, v___y_2687_, v___x_2689_);
lean_dec(v___y_2687_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2690_);
lean_ctor_set(v___x_2678_, 0, v___y_2686_);
v___x_2692_ = v___x_2678_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___y_2686_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_auxDeclToFullName_2675_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v_index_2698_; 
lean_inc_ref(v_decl_2684_);
v___x_2697_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2673_, v___y_2696_, v_decl_2684_);
v_index_2698_ = lean_ctor_get(v_decl_2684_, 0);
lean_inc(v_index_2698_);
v___y_2686_ = v___x_2697_;
v___y_2687_ = v_index_2698_;
goto v___jp_2685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2705_, lean_object* v_fvarId_2706_, lean_object* v_bi_2707_){
_start:
{
uint8_t v_bi_boxed_2708_; lean_object* v_res_2709_; 
v_bi_boxed_2708_ = lean_unbox(v_bi_2707_);
v_res_2709_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2705_, v_fvarId_2706_, v_bi_boxed_2708_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2710_, lean_object* v_fvarId_2711_, lean_object* v_type_2712_){
_start:
{
lean_object* v_fvarIdToDecl_2713_; lean_object* v_decls_2714_; lean_object* v_auxDeclToFullName_2715_; lean_object* v___x_2716_; 
v_fvarIdToDecl_2713_ = lean_ctor_get(v_lctx_2710_, 0);
v_decls_2714_ = lean_ctor_get(v_lctx_2710_, 1);
v_auxDeclToFullName_2715_ = lean_ctor_get(v_lctx_2710_, 2);
lean_inc_ref(v_lctx_2710_);
v___x_2716_ = lean_local_ctx_find(v_lctx_2710_, v_fvarId_2711_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref(v_type_2712_);
return v_lctx_2710_;
}
else
{
lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2741_; 
lean_inc(v_auxDeclToFullName_2715_);
lean_inc_ref(v_decls_2714_);
lean_inc_ref(v_fvarIdToDecl_2713_);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_lctx_2710_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; lean_object* v_unused_2743_; lean_object* v_unused_2744_; 
v_unused_2742_ = lean_ctor_get(v_lctx_2710_, 2);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_lctx_2710_, 1);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_lctx_2710_, 0);
lean_dec(v_unused_2744_);
v___x_2718_ = v_lctx_2710_;
v_isShared_2719_ = v_isSharedCheck_2741_;
goto v_resetjp_2717_;
}
else
{
lean_dec(v_lctx_2710_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2741_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_val_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2740_; 
v_val_2720_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2722_ = v___x_2716_;
v_isShared_2723_ = v_isSharedCheck_2740_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_val_2720_);
lean_dec(v___x_2716_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2740_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_decl_2724_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2736_; lean_object* v_fvarId_2739_; 
v_decl_2724_ = l_Lean_LocalDecl_setType(v_val_2720_, v_type_2712_);
v_fvarId_2739_ = lean_ctor_get(v_decl_2724_, 1);
lean_inc(v_fvarId_2739_);
v___y_2736_ = v_fvarId_2739_;
goto v___jp_2735_;
v___jp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v_decl_2724_);
v___x_2729_ = v___x_2722_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_decl_2724_);
v___x_2729_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = l_Lean_PersistentArray_set___redArg(v_decls_2714_, v___y_2727_, v___x_2729_);
lean_dec(v___y_2727_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2730_);
lean_ctor_set(v___x_2718_, 0, v___y_2726_);
v___x_2732_ = v___x_2718_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___y_2726_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_auxDeclToFullName_2715_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
v___jp_2735_:
{
lean_object* v___x_2737_; lean_object* v_index_2738_; 
lean_inc_ref(v_decl_2724_);
v___x_2737_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2713_, v___y_2736_, v_decl_2724_);
v_index_2738_ = lean_ctor_get(v_decl_2724_, 0);
lean_inc(v_index_2738_);
v___y_2726_ = v___x_2737_;
v___y_2727_ = v_index_2738_;
goto v___jp_2725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2745_){
_start:
{
lean_object* v_decls_2746_; lean_object* v_size_2747_; 
v_decls_2746_ = lean_ctor_get(v_lctx_2745_, 1);
lean_inc_ref(v_decls_2746_);
lean_dec_ref(v_lctx_2745_);
v_size_2747_ = lean_ctor_get(v_decls_2746_, 2);
lean_inc(v_size_2747_);
lean_dec_ref(v_decls_2746_);
return v_size_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2748_, lean_object* v_i_2749_){
_start:
{
lean_object* v_decls_2750_; lean_object* v_size_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v_decls_2750_ = lean_ctor_get(v_lctx_2748_, 1);
v_size_2751_ = lean_ctor_get(v_decls_2750_, 2);
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_nat_dec_lt(v_i_2749_, v_size_2751_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l_outOfBounds___redArg(v___x_2752_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2752_, v_decls_2750_, v_i_2749_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2756_, lean_object* v_i_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2756_, v_i_2757_);
lean_dec(v_i_2757_);
lean_dec_ref(v_lctx_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2759_, lean_object* v_f_2760_, lean_object* v_b_2761_, lean_object* v_decl_2762_){
_start:
{
if (lean_obj_tag(v_decl_2762_) == 0)
{
lean_object* v___x_2763_; 
lean_dec(v_f_2760_);
v___x_2763_ = lean_apply_2(v_toPure_2759_, lean_box(0), v_b_2761_);
return v___x_2763_;
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2765_; 
lean_dec(v_toPure_2759_);
v_val_2764_ = lean_ctor_get(v_decl_2762_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_decl_2762_, 1);
v___x_2765_ = lean_apply_2(v_f_2760_, v_b_2761_, v_val_2764_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2766_, lean_object* v_lctx_2767_, lean_object* v_f_2768_, lean_object* v_init_2769_, lean_object* v_start_2770_){
_start:
{
lean_object* v_toApplicative_2771_; lean_object* v_decls_2772_; lean_object* v_toPure_2773_; lean_object* v___f_2774_; lean_object* v___x_2775_; 
v_toApplicative_2771_ = lean_ctor_get(v_inst_2766_, 0);
v_decls_2772_ = lean_ctor_get(v_lctx_2767_, 1);
lean_inc_ref(v_decls_2772_);
lean_dec_ref(v_lctx_2767_);
v_toPure_2773_ = lean_ctor_get(v_toApplicative_2771_, 1);
lean_inc(v_toPure_2773_);
v___f_2774_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2774_, 0, v_toPure_2773_);
lean_closure_set(v___f_2774_, 1, v_f_2768_);
v___x_2775_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2766_, v_decls_2772_, v___f_2774_, v_init_2769_, v_start_2770_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2776_, lean_object* v_lctx_2777_, lean_object* v_f_2778_, lean_object* v_init_2779_, lean_object* v_start_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2776_, v_lctx_2777_, v_f_2778_, v_init_2779_, v_start_2780_);
lean_dec(v_start_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_inst_2784_, lean_object* v_lctx_2785_, lean_object* v_f_2786_, lean_object* v_init_2787_, lean_object* v_start_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2784_, v_lctx_2785_, v_f_2786_, v_init_2787_, v_start_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2790_, lean_object* v_00_u03b2_2791_, lean_object* v_inst_2792_, lean_object* v_lctx_2793_, lean_object* v_f_2794_, lean_object* v_init_2795_, lean_object* v_start_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_LocalContext_foldlM(v_m_2790_, v_00_u03b2_2791_, v_inst_2792_, v_lctx_2793_, v_f_2794_, v_init_2795_, v_start_2796_);
lean_dec(v_start_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2798_, lean_object* v_f_2799_, lean_object* v_decl_2800_, lean_object* v_b_2801_){
_start:
{
if (lean_obj_tag(v_decl_2800_) == 0)
{
lean_object* v___x_2802_; 
lean_dec(v_f_2799_);
v___x_2802_ = lean_apply_2(v_toPure_2798_, lean_box(0), v_b_2801_);
return v___x_2802_;
}
else
{
lean_object* v_val_2803_; lean_object* v___x_2804_; 
lean_dec(v_toPure_2798_);
v_val_2803_ = lean_ctor_get(v_decl_2800_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_decl_2800_, 1);
v___x_2804_ = lean_apply_2(v_f_2799_, v_val_2803_, v_b_2801_);
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2805_, lean_object* v_lctx_2806_, lean_object* v_f_2807_, lean_object* v_init_2808_){
_start:
{
lean_object* v_toApplicative_2809_; lean_object* v_decls_2810_; lean_object* v_toPure_2811_; lean_object* v___f_2812_; lean_object* v___x_2813_; 
v_toApplicative_2809_ = lean_ctor_get(v_inst_2805_, 0);
v_decls_2810_ = lean_ctor_get(v_lctx_2806_, 1);
lean_inc_ref(v_decls_2810_);
lean_dec_ref(v_lctx_2806_);
v_toPure_2811_ = lean_ctor_get(v_toApplicative_2809_, 1);
lean_inc(v_toPure_2811_);
v___f_2812_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2812_, 0, v_toPure_2811_);
lean_closure_set(v___f_2812_, 1, v_f_2807_);
v___x_2813_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2805_, v_decls_2810_, v___f_2812_, v_init_2808_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2814_, lean_object* v_00_u03b2_2815_, lean_object* v_inst_2816_, lean_object* v_lctx_2817_, lean_object* v_f_2818_, lean_object* v_init_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2816_, v_lctx_2817_, v_f_2818_, v_init_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2821_, lean_object* v_f_2822_, lean_object* v_decl_2823_){
_start:
{
if (lean_obj_tag(v_decl_2823_) == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v_f_2822_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_apply_2(v_toPure_2821_, lean_box(0), v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v_val_2826_; lean_object* v___x_2827_; 
lean_dec(v_toPure_2821_);
v_val_2826_ = lean_ctor_get(v_decl_2823_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_decl_2823_, 1);
v___x_2827_ = lean_apply_1(v_f_2822_, v_val_2826_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2828_, lean_object* v_lctx_2829_, lean_object* v_f_2830_, lean_object* v_start_2831_){
_start:
{
lean_object* v_toApplicative_2832_; lean_object* v_decls_2833_; lean_object* v_toPure_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; 
v_toApplicative_2832_ = lean_ctor_get(v_inst_2828_, 0);
v_decls_2833_ = lean_ctor_get(v_lctx_2829_, 1);
lean_inc_ref(v_decls_2833_);
lean_dec_ref(v_lctx_2829_);
v_toPure_2834_ = lean_ctor_get(v_toApplicative_2832_, 1);
lean_inc(v_toPure_2834_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2835_, 0, v_toPure_2834_);
lean_closure_set(v___f_2835_, 1, v_f_2830_);
v___x_2836_ = l_Lean_PersistentArray_forM___redArg(v_inst_2828_, v_decls_2833_, v___f_2835_, v_start_2831_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2837_, lean_object* v_lctx_2838_, lean_object* v_f_2839_, lean_object* v_start_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_LocalContext_forM___redArg(v_inst_2837_, v_lctx_2838_, v_f_2839_, v_start_2840_);
lean_dec(v_start_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2842_, lean_object* v_inst_2843_, lean_object* v_lctx_2844_, lean_object* v_f_2845_, lean_object* v_start_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_LocalContext_forM___redArg(v_inst_2843_, v_lctx_2844_, v_f_2845_, v_start_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2848_, lean_object* v_inst_2849_, lean_object* v_lctx_2850_, lean_object* v_f_2851_, lean_object* v_start_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_LocalContext_forM(v_m_2848_, v_inst_2849_, v_lctx_2850_, v_f_2851_, v_start_2852_);
lean_dec(v_start_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2854_, lean_object* v_f_2855_, lean_object* v_decl_2856_){
_start:
{
if (lean_obj_tag(v_decl_2856_) == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec(v_f_2855_);
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_apply_2(v_toPure_2854_, lean_box(0), v___x_2857_);
return v___x_2858_;
}
else
{
lean_object* v_val_2859_; lean_object* v___x_2860_; 
lean_dec(v_toPure_2854_);
v_val_2859_ = lean_ctor_get(v_decl_2856_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v_decl_2856_, 1);
v___x_2860_ = lean_apply_1(v_f_2855_, v_val_2859_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2861_, lean_object* v_lctx_2862_, lean_object* v_f_2863_){
_start:
{
lean_object* v_toApplicative_2864_; lean_object* v_decls_2865_; lean_object* v_toPure_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; 
v_toApplicative_2864_ = lean_ctor_get(v_inst_2861_, 0);
v_decls_2865_ = lean_ctor_get(v_lctx_2862_, 1);
lean_inc_ref(v_decls_2865_);
lean_dec_ref(v_lctx_2862_);
v_toPure_2866_ = lean_ctor_get(v_toApplicative_2864_, 1);
lean_inc(v_toPure_2866_);
v___f_2867_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2867_, 0, v_toPure_2866_);
lean_closure_set(v___f_2867_, 1, v_f_2863_);
v___x_2868_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2861_, v_decls_2865_, v___f_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_inst_2871_, lean_object* v_lctx_2872_, lean_object* v_f_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2871_, v_lctx_2872_, v_f_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2875_, lean_object* v_lctx_2876_, lean_object* v_f_2877_){
_start:
{
lean_object* v_toApplicative_2878_; lean_object* v_decls_2879_; lean_object* v_toPure_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; 
v_toApplicative_2878_ = lean_ctor_get(v_inst_2875_, 0);
v_decls_2879_ = lean_ctor_get(v_lctx_2876_, 1);
lean_inc_ref(v_decls_2879_);
lean_dec_ref(v_lctx_2876_);
v_toPure_2880_ = lean_ctor_get(v_toApplicative_2878_, 1);
lean_inc(v_toPure_2880_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2881_, 0, v_toPure_2880_);
lean_closure_set(v___f_2881_, 1, v_f_2877_);
v___x_2882_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2875_, v_decls_2879_, v___f_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2883_, lean_object* v_00_u03b2_2884_, lean_object* v_inst_2885_, lean_object* v_lctx_2886_, lean_object* v_f_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2885_, v_lctx_2886_, v_f_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2889_, lean_object* v_f_2890_, lean_object* v_d_x3f_2891_, lean_object* v_b_2892_){
_start:
{
if (lean_obj_tag(v_d_x3f_2891_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v_f_2890_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_b_2892_);
v___x_2894_ = lean_apply_2(v_toPure_2889_, lean_box(0), v___x_2893_);
return v___x_2894_;
}
else
{
lean_object* v_val_2895_; lean_object* v___x_2896_; 
lean_dec(v_toPure_2889_);
v_val_2895_ = lean_ctor_get(v_d_x3f_2891_, 0);
lean_inc(v_val_2895_);
lean_dec_ref_known(v_d_x3f_2891_, 1);
v___x_2896_ = lean_apply_2(v_f_2890_, v_val_2895_, v_b_2892_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2897_, lean_object* v_inst_2898_, lean_object* v_00_u03b2_2899_, lean_object* v_lctx_2900_, lean_object* v_init_2901_, lean_object* v_f_2902_){
_start:
{
lean_object* v_decls_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; 
v_decls_2903_ = lean_ctor_get(v_lctx_2900_, 1);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2904_, 0, v_toPure_2897_);
lean_closure_set(v___f_2904_, 1, v_f_2902_);
v___x_2905_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2898_, v_decls_2903_, v_init_2901_, v___f_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2906_, lean_object* v_inst_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_lctx_2909_, lean_object* v_init_2910_, lean_object* v_f_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2906_, v_inst_2907_, v_00_u03b2_2908_, v_lctx_2909_, v_init_2910_, v_f_2911_);
lean_dec_ref(v_lctx_2909_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2913_){
_start:
{
lean_object* v_toApplicative_2914_; lean_object* v_toPure_2915_; lean_object* v___f_2916_; 
v_toApplicative_2914_ = lean_ctor_get(v_inst_2913_, 0);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2914_, 1);
lean_inc(v_toPure_2915_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2916_, 0, v_toPure_2915_);
lean_closure_set(v___f_2916_, 1, v_inst_2913_);
return v___f_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2917_, lean_object* v_inst_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2920_, lean_object* v_x1_2921_, lean_object* v_x2_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_apply_2(v_f_2920_, v_x1_2921_, v_x2_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2943_, lean_object* v_f_2944_, lean_object* v_init_2945_, lean_object* v_start_2946_){
_start:
{
lean_object* v___f_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2947_, 0, v_f_2944_);
v___x_2948_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2949_ = l_Lean_LocalContext_foldlM___redArg(v___x_2948_, v_lctx_2943_, v___f_2947_, v_init_2945_, v_start_2946_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2950_, lean_object* v_f_2951_, lean_object* v_init_2952_, lean_object* v_start_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2950_, v_f_2951_, v_init_2952_, v_start_2953_);
lean_dec(v_start_2953_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2955_, lean_object* v_lctx_2956_, lean_object* v_f_2957_, lean_object* v_init_2958_, lean_object* v_start_2959_){
_start:
{
lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2960_, 0, v_f_2957_);
v___x_2961_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2962_ = l_Lean_LocalContext_foldlM___redArg(v___x_2961_, v_lctx_2956_, v___f_2960_, v_init_2958_, v_start_2959_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2963_, lean_object* v_lctx_2964_, lean_object* v_f_2965_, lean_object* v_init_2966_, lean_object* v_start_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_LocalContext_foldl(v_00_u03b2_2963_, v_lctx_2964_, v_f_2965_, v_init_2966_, v_start_2967_);
lean_dec(v_start_2967_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2969_, lean_object* v_x1_2970_, lean_object* v_x2_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_apply_2(v_f_2969_, v_x1_2970_, v_x2_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2973_, lean_object* v_f_2974_, lean_object* v_init_2975_){
_start:
{
lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2976_, 0, v_f_2974_);
v___x_2977_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2978_ = l_Lean_LocalContext_foldrM___redArg(v___x_2977_, v_lctx_2973_, v___f_2976_, v_init_2975_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2979_, lean_object* v_lctx_2980_, lean_object* v_f_2981_, lean_object* v_init_2982_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_2986_, size_t v_i_2987_, size_t v_stop_2988_, lean_object* v_b_2989_){
_start:
{
lean_object* v___y_2991_; uint8_t v___x_2995_; 
v___x_2995_ = lean_usize_dec_eq(v_i_2987_, v_stop_2988_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_array_uget_borrowed(v_as_2986_, v_i_2987_);
if (lean_obj_tag(v___x_2996_) == 0)
{
v___y_2991_ = v_b_2989_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_unsigned_to_nat(1u);
v___x_2998_ = lean_nat_add(v_b_2989_, v___x_2997_);
lean_dec(v_b_2989_);
v___y_2991_ = v___x_2998_;
goto v___jp_2990_;
}
}
else
{
return v_b_2989_;
}
v___jp_2990_:
{
size_t v___x_2992_; size_t v___x_2993_; 
v___x_2992_ = ((size_t)1ULL);
v___x_2993_ = lean_usize_add(v_i_2987_, v___x_2992_);
v_i_2987_ = v___x_2993_;
v_b_2989_ = v___y_2991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2999_, lean_object* v_i_3000_, lean_object* v_stop_3001_, lean_object* v_b_3002_){
_start:
{
size_t v_i_boxed_3003_; size_t v_stop_boxed_3004_; lean_object* v_res_3005_; 
v_i_boxed_3003_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_stop_boxed_3004_ = lean_unbox_usize(v_stop_3001_);
lean_dec(v_stop_3001_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_2999_, v_i_boxed_3003_, v_stop_boxed_3004_, v_b_3002_);
lean_dec_ref(v_as_2999_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3006_, lean_object* v_x_3007_){
_start:
{
if (lean_obj_tag(v_x_3006_) == 0)
{
lean_object* v_cs_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_cs_3008_ = lean_ctor_get(v_x_3006_, 0);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_array_get_size(v_cs_3008_);
v___x_3011_ = lean_nat_dec_lt(v___x_3009_, v___x_3010_);
if (v___x_3011_ == 0)
{
return v_x_3007_;
}
else
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = lean_usize_of_nat(v___x_3010_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3008_, v___x_3012_, v___x_3013_, v_x_3007_);
return v___x_3014_;
}
}
else
{
lean_object* v_vs_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_vs_3015_ = lean_ctor_get(v_x_3006_, 0);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_vs_3015_);
v___x_3018_ = lean_nat_dec_lt(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
return v_x_3007_;
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3017_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3015_, v___x_3019_, v___x_3020_, v_x_3007_);
return v___x_3021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3022_, size_t v_i_3023_, size_t v_stop_3024_, lean_object* v_b_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_eq(v_i_3023_, v_stop_3024_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; 
v___x_3027_ = lean_array_uget_borrowed(v_as_3022_, v_i_3023_);
v___x_3028_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3027_, v_b_3025_);
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_add(v_i_3023_, v___x_3029_);
v_i_3023_ = v___x_3030_;
v_b_3025_ = v___x_3028_;
goto _start;
}
else
{
return v_b_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_, lean_object* v_b_3035_){
_start:
{
size_t v_i_boxed_3036_; size_t v_stop_boxed_3037_; lean_object* v_res_3038_; 
v_i_boxed_3036_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3037_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3032_, v_i_boxed_3036_, v_stop_boxed_3037_, v_b_3035_);
lean_dec_ref(v_as_3032_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3039_, v_x_3040_);
lean_dec_ref(v_x_3039_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3042_, size_t v_x_3043_, size_t v_x_3044_, lean_object* v_x_3045_){
_start:
{
if (lean_obj_tag(v_x_3042_) == 0)
{
lean_object* v_cs_3046_; lean_object* v___x_3047_; size_t v___x_3048_; lean_object* v_j_3049_; lean_object* v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; size_t v___x_3053_; size_t v___x_3054_; size_t v___x_3055_; size_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_cs_3046_ = lean_ctor_get(v_x_3042_, 0);
v___x_3047_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3048_ = lean_usize_shift_right(v_x_3043_, v_x_3044_);
v_j_3049_ = lean_usize_to_nat(v___x_3048_);
v___x_3050_ = lean_array_get_borrowed(v___x_3047_, v_cs_3046_, v_j_3049_);
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_shift_left(v___x_3051_, v_x_3044_);
v___x_3053_ = lean_usize_sub(v___x_3052_, v___x_3051_);
v___x_3054_ = lean_usize_land(v_x_3043_, v___x_3053_);
v___x_3055_ = ((size_t)5ULL);
v___x_3056_ = lean_usize_sub(v_x_3044_, v___x_3055_);
v___x_3057_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3050_, v___x_3054_, v___x_3056_, v_x_3045_);
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_add(v_j_3049_, v___x_3058_);
lean_dec(v_j_3049_);
v___x_3060_ = lean_array_get_size(v_cs_3046_);
v___x_3061_ = lean_nat_dec_lt(v___x_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_dec(v___x_3059_);
return v___x_3057_;
}
else
{
size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_usize_of_nat(v___x_3059_);
lean_dec(v___x_3059_);
v___x_3063_ = lean_usize_of_nat(v___x_3060_);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3046_, v___x_3062_, v___x_3063_, v___x_3057_);
return v___x_3064_;
}
}
else
{
lean_object* v_vs_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_vs_3065_ = lean_ctor_get(v_x_3042_, 0);
v___x_3066_ = lean_usize_to_nat(v_x_3043_);
v___x_3067_ = lean_array_get_size(v_vs_3065_);
v___x_3068_ = lean_nat_dec_lt(v___x_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_dec(v___x_3066_);
return v_x_3045_;
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_usize_of_nat(v___x_3066_);
lean_dec(v___x_3066_);
v___x_3070_ = lean_usize_of_nat(v___x_3067_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3065_, v___x_3069_, v___x_3070_, v_x_3045_);
return v___x_3071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_, lean_object* v_x_3075_){
_start:
{
size_t v_x_1185__boxed_3076_; size_t v_x_1186__boxed_3077_; lean_object* v_res_3078_; 
v_x_1185__boxed_3076_ = lean_unbox_usize(v_x_3073_);
lean_dec(v_x_3073_);
v_x_1186__boxed_3077_ = lean_unbox_usize(v_x_3074_);
lean_dec(v_x_3074_);
v_res_3078_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3072_, v_x_1185__boxed_3076_, v_x_1186__boxed_3077_, v_x_3075_);
lean_dec_ref(v_x_3072_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3079_, lean_object* v_init_3080_, lean_object* v_start_3081_){
_start:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_nat_dec_eq(v_start_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v_root_3084_; lean_object* v_tail_3085_; size_t v_shift_3086_; lean_object* v_tailOff_3087_; uint8_t v___x_3088_; 
v_root_3084_ = lean_ctor_get(v_t_3079_, 0);
v_tail_3085_ = lean_ctor_get(v_t_3079_, 1);
v_shift_3086_ = lean_ctor_get_usize(v_t_3079_, 4);
v_tailOff_3087_ = lean_ctor_get(v_t_3079_, 3);
v___x_3088_ = lean_nat_dec_le(v_tailOff_3087_, v_start_3081_);
if (v___x_3088_ == 0)
{
size_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3089_ = lean_usize_of_nat(v_start_3081_);
v___x_3090_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3084_, v___x_3089_, v_shift_3086_, v_init_3080_);
v___x_3091_ = lean_array_get_size(v_tail_3085_);
v___x_3092_ = lean_nat_dec_lt(v___x_3082_, v___x_3091_);
if (v___x_3092_ == 0)
{
return v___x_3090_;
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = lean_usize_of_nat(v___x_3091_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3085_, v___x_3093_, v___x_3094_, v___x_3090_);
return v___x_3095_;
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3096_ = lean_nat_sub(v_start_3081_, v_tailOff_3087_);
v___x_3097_ = lean_array_get_size(v_tail_3085_);
v___x_3098_ = lean_nat_dec_lt(v___x_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_dec(v___x_3096_);
return v_init_3080_;
}
else
{
size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_usize_of_nat(v___x_3096_);
lean_dec(v___x_3096_);
v___x_3100_ = lean_usize_of_nat(v___x_3097_);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3085_, v___x_3099_, v___x_3100_, v_init_3080_);
return v___x_3101_;
}
}
}
else
{
lean_object* v_root_3102_; lean_object* v_tail_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_root_3102_ = lean_ctor_get(v_t_3079_, 0);
v_tail_3103_ = lean_ctor_get(v_t_3079_, 1);
v___x_3104_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3102_, v_init_3080_);
v___x_3105_ = lean_array_get_size(v_tail_3103_);
v___x_3106_ = lean_nat_dec_lt(v___x_3082_, v___x_3105_);
if (v___x_3106_ == 0)
{
return v___x_3104_;
}
else
{
size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = lean_usize_of_nat(v___x_3105_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3103_, v___x_3107_, v___x_3108_, v___x_3104_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3110_, lean_object* v_init_3111_, lean_object* v_start_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3110_, v_init_3111_, v_start_3112_);
lean_dec(v_start_3112_);
lean_dec_ref(v_t_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3114_, lean_object* v_init_3115_, lean_object* v_start_3116_){
_start:
{
lean_object* v_decls_3117_; lean_object* v___x_3118_; 
v_decls_3117_ = lean_ctor_get(v_lctx_3114_, 1);
v___x_3118_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3117_, v_init_3115_, v_start_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3119_, lean_object* v_init_3120_, lean_object* v_start_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3119_, v_init_3120_, v_start_3121_);
lean_dec(v_start_3121_);
lean_dec_ref(v_lctx_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3123_){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3123_, v___x_3124_, v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_LocalContext_size(v_lctx_3126_);
lean_dec_ref(v_lctx_3126_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_apply_1(v_f_3128_, v_x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3131_, lean_object* v_f_3132_){
_start:
{
lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3133_, 0, v_f_3132_);
v___x_3134_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3135_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3134_, v_lctx_3131_, v___f_3133_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3136_, lean_object* v_lctx_3137_, lean_object* v_f_3138_){
_start:
{
lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3139_, 0, v_f_3138_);
v___x_3140_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3141_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3140_, v_lctx_3137_, v___f_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3142_, lean_object* v_f_3143_){
_start:
{
lean_object* v___f_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___f_3144_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3144_, 0, v_f_3143_);
v___x_3145_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3146_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3145_, v_lctx_3142_, v___f_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3147_, lean_object* v_lctx_3148_, lean_object* v_f_3149_){
_start:
{
lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3150_, 0, v_f_3149_);
v___x_3151_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3152_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3151_, v_lctx_3148_, v___f_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3153_, lean_object* v_as_3154_, size_t v_i_3155_, size_t v_stop_3156_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_usize_dec_eq(v_i_3155_, v_stop_3156_);
if (v___x_3157_ == 0)
{
uint8_t v___x_3158_; uint8_t v___y_3160_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_fvarId_3166_; uint8_t v___x_3167_; 
v___x_3158_ = 1;
v___x_3164_ = lean_array_uget_borrowed(v_as_3154_, v_i_3155_);
v___x_3165_ = l_Lean_Expr_fvarId_x21(v___x_3164_);
v_fvarId_3166_ = lean_ctor_get(v_val_3153_, 1);
v___x_3167_ = l_Lean_instBEqFVarId_beq(v___x_3165_, v_fvarId_3166_);
lean_dec(v___x_3165_);
v___y_3160_ = v___x_3167_;
goto v___jp_3159_;
v___jp_3159_:
{
if (v___y_3160_ == 0)
{
size_t v___x_3161_; size_t v___x_3162_; 
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3155_, v___x_3161_);
v_i_3155_ = v___x_3162_;
goto _start;
}
else
{
return v___x_3158_;
}
}
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = 0;
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3169_, lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_stop_3172_){
_start:
{
size_t v_i_boxed_3173_; size_t v_stop_boxed_3174_; uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_i_boxed_3173_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_stop_boxed_3174_ = lean_unbox_usize(v_stop_3172_);
lean_dec(v_stop_3172_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3169_, v_as_3170_, v_i_boxed_3173_, v_stop_boxed_3174_);
lean_dec_ref(v_as_3170_);
lean_dec_ref(v_val_3169_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3177_, lean_object* v_a_u2082_3178_, lean_object* v_exceptFVars_3179_, lean_object* v_i_3180_, lean_object* v_j_3181_){
_start:
{
lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v_size_3197_; uint8_t v___x_3198_; 
v_size_3197_ = lean_ctor_get(v_a_u2081_3177_, 2);
v___x_3198_ = lean_nat_dec_lt(v_i_3180_, v_size_3197_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; 
lean_dec(v_j_3181_);
lean_dec(v_i_3180_);
v___x_3199_ = 1;
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_box(0);
v___x_3201_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3200_, v_a_u2081_3177_, v_i_3180_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_unsigned_to_nat(1u);
v___x_3203_ = lean_nat_add(v_i_3180_, v___x_3202_);
lean_dec(v_i_3180_);
v_i_3180_ = v___x_3203_;
goto _start;
}
else
{
lean_object* v_val_3205_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v_val_3205_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v___x_3201_, 1);
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = lean_array_get_size(v_exceptFVars_3179_);
v___x_3217_ = lean_nat_dec_lt(v___x_3215_, v___x_3216_);
if (v___x_3217_ == 0)
{
goto v___jp_3206_;
}
else
{
if (v___x_3217_ == 0)
{
goto v___jp_3206_;
}
else
{
size_t v___x_3218_; size_t v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = ((size_t)0ULL);
v___x_3219_ = lean_usize_of_nat(v___x_3216_);
v___x_3220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3205_, v_exceptFVars_3179_, v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
goto v___jp_3206_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec(v_val_3205_);
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_add(v_i_3180_, v___x_3221_);
lean_dec(v_i_3180_);
v_i_3180_ = v___x_3222_;
goto _start;
}
}
}
v___jp_3206_:
{
lean_object* v_size_3207_; uint8_t v___x_3208_; 
v_size_3207_ = lean_ctor_get(v_a_u2082_3178_, 2);
v___x_3208_ = lean_nat_dec_lt(v_j_3181_, v_size_3207_);
if (v___x_3208_ == 0)
{
lean_dec(v_val_3205_);
lean_dec(v_j_3181_);
lean_dec(v_i_3180_);
return v___x_3208_;
}
else
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3200_, v_a_u2082_3178_, v_j_3181_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v_val_3205_);
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_j_3181_, v___x_3210_);
lean_dec(v_j_3181_);
v_j_3181_ = v___x_3211_;
goto _start;
}
else
{
lean_object* v_val_3213_; lean_object* v_fvarId_3214_; 
v_val_3213_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v___x_3209_, 1);
v_fvarId_3214_ = lean_ctor_get(v_val_3205_, 1);
lean_inc(v_fvarId_3214_);
lean_dec(v_val_3205_);
v___y_3194_ = v_val_3213_;
v___y_3195_ = v_fvarId_3214_;
goto v___jp_3193_;
}
}
}
}
}
v___jp_3182_:
{
uint8_t v___x_3185_; 
v___x_3185_ = l_Lean_instBEqFVarId_beq(v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec(v___y_3183_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_unsigned_to_nat(1u);
v___x_3187_ = lean_nat_add(v_j_3181_, v___x_3186_);
lean_dec(v_j_3181_);
v_j_3181_ = v___x_3187_;
goto _start;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3190_ = lean_nat_add(v_i_3180_, v___x_3189_);
lean_dec(v_i_3180_);
v___x_3191_ = lean_nat_add(v_j_3181_, v___x_3189_);
lean_dec(v_j_3181_);
v_i_3180_ = v___x_3190_;
v_j_3181_ = v___x_3191_;
goto _start;
}
}
v___jp_3193_:
{
lean_object* v_fvarId_3196_; 
v_fvarId_3196_ = lean_ctor_get(v___y_3194_, 1);
lean_inc(v_fvarId_3196_);
lean_dec_ref(v___y_3194_);
v___y_3183_ = v___y_3195_;
v___y_3184_ = v_fvarId_3196_;
goto v___jp_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3224_, lean_object* v_a_u2082_3225_, lean_object* v_exceptFVars_3226_, lean_object* v_i_3227_, lean_object* v_j_3228_){
_start:
{
uint8_t v_res_3229_; lean_object* v_r_3230_; 
v_res_3229_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3224_, v_a_u2082_3225_, v_exceptFVars_3226_, v_i_3227_, v_j_3228_);
lean_dec_ref(v_exceptFVars_3226_);
lean_dec_ref(v_a_u2082_3225_);
lean_dec_ref(v_a_u2081_3224_);
v_r_3230_ = lean_box(v_res_3229_);
return v_r_3230_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3231_, lean_object* v_lctx_u2082_3232_, lean_object* v_exceptFVars_3233_){
_start:
{
lean_object* v_decls_3234_; lean_object* v_decls_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_decls_3234_ = lean_ctor_get(v_lctx_u2081_3231_, 1);
v_decls_3235_ = lean_ctor_get(v_lctx_u2082_3232_, 1);
v___x_3236_ = lean_unsigned_to_nat(0u);
v___x_3237_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3234_, v_decls_3235_, v_exceptFVars_3233_, v___x_3236_, v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3238_, lean_object* v_lctx_u2082_3239_, lean_object* v_exceptFVars_3240_){
_start:
{
uint8_t v_res_3241_; lean_object* v_r_3242_; 
v_res_3241_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3238_, v_lctx_u2082_3239_, v_exceptFVars_3240_);
lean_dec_ref(v_exceptFVars_3240_);
lean_dec_ref(v_lctx_u2082_3239_);
lean_dec_ref(v_lctx_u2081_3238_);
v_r_3242_ = lean_box(v_res_3241_);
return v_r_3242_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3244_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3245_ = lean_unsigned_to_nat(14u);
v___x_3246_ = lean_unsigned_to_nat(574u);
v___x_3247_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3248_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3249_ = l_mkPanicMessageWithDecl(v___x_3248_, v___x_3247_, v___x_3246_, v___x_3245_, v___x_3244_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3250_, lean_object* v_lctx_3251_, lean_object* v___x_3252_, uint8_t v_isLambda_3253_, uint8_t v_usedLetOnly_3254_, uint8_t v_generalizeNondepLet_3255_, lean_object* v_i_3256_, lean_object* v_x_3257_, lean_object* v_b_3258_){
_start:
{
lean_object* v_n_3260_; lean_object* v_ty_3261_; uint8_t v_bi_3262_; lean_object* v_x_3266_; lean_object* v___x_3267_; 
v_x_3266_ = lean_array_fget_borrowed(v_xs_3250_, v_i_3256_);
v___x_3267_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3251_, v_x_3266_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec_ref(v_b_3258_);
v___x_3268_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3269_ = l_panic___redArg(v___x_3252_, v___x_3268_);
return v___x_3269_;
}
else
{
lean_object* v_val_3270_; 
v_val_3270_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___x_3267_, 1);
if (lean_obj_tag(v_val_3270_) == 0)
{
lean_object* v_userName_3271_; lean_object* v_type_3272_; uint8_t v_bi_3273_; 
v_userName_3271_ = lean_ctor_get(v_val_3270_, 2);
lean_inc(v_userName_3271_);
v_type_3272_ = lean_ctor_get(v_val_3270_, 3);
lean_inc_ref(v_type_3272_);
v_bi_3273_ = lean_ctor_get_uint8(v_val_3270_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3270_, 4);
v_n_3260_ = v_userName_3271_;
v_ty_3261_ = v_type_3272_;
v_bi_3262_ = v_bi_3273_;
goto v___jp_3259_;
}
else
{
lean_object* v_userName_3274_; lean_object* v_type_3275_; lean_object* v_value_3276_; uint8_t v_nondep_3277_; uint8_t v___y_3283_; 
v_userName_3274_ = lean_ctor_get(v_val_3270_, 2);
lean_inc(v_userName_3274_);
v_type_3275_ = lean_ctor_get(v_val_3270_, 3);
lean_inc_ref(v_type_3275_);
v_value_3276_ = lean_ctor_get(v_val_3270_, 4);
lean_inc_ref(v_value_3276_);
v_nondep_3277_ = lean_ctor_get_uint8(v_val_3270_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3270_, 5);
if (v_nondep_3277_ == 0)
{
v___y_3283_ = v_nondep_3277_;
goto v___jp_3282_;
}
else
{
if (v_generalizeNondepLet_3255_ == 0)
{
v___y_3283_ = v_generalizeNondepLet_3255_;
goto v___jp_3282_;
}
else
{
uint8_t v___x_3288_; 
lean_dec_ref(v_value_3276_);
v___x_3288_ = 0;
v_n_3260_ = v_userName_3274_;
v_ty_3261_ = v_type_3275_;
v_bi_3262_ = v___x_3288_;
goto v___jp_3259_;
}
}
v___jp_3278_:
{
lean_object* v_ty_3279_; lean_object* v_val_3280_; lean_object* v___x_3281_; 
v_ty_3279_ = lean_expr_abstract_range(v_type_3275_, v_i_3256_, v_xs_3250_);
lean_dec_ref(v_type_3275_);
v_val_3280_ = lean_expr_abstract_range(v_value_3276_, v_i_3256_, v_xs_3250_);
lean_dec_ref(v_value_3276_);
v___x_3281_ = l_Lean_Expr_letE___override(v_userName_3274_, v_ty_3279_, v_val_3280_, v_b_3258_, v_nondep_3277_);
return v___x_3281_;
}
v___jp_3282_:
{
if (v_usedLetOnly_3254_ == 0)
{
goto v___jp_3278_;
}
else
{
if (v___y_3283_ == 0)
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = lean_expr_has_loose_bvar(v_b_3258_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec_ref(v_value_3276_);
lean_dec_ref(v_type_3275_);
lean_dec(v_userName_3274_);
v___x_3286_ = lean_unsigned_to_nat(1u);
v___x_3287_ = lean_expr_lower_loose_bvars(v_b_3258_, v___x_3286_, v___x_3286_);
lean_dec_ref(v_b_3258_);
return v___x_3287_;
}
else
{
goto v___jp_3278_;
}
}
else
{
goto v___jp_3278_;
}
}
}
}
}
v___jp_3259_:
{
lean_object* v_ty_3263_; 
v_ty_3263_ = lean_expr_abstract_range(v_ty_3261_, v_i_3256_, v_xs_3250_);
lean_dec_ref(v_ty_3261_);
if (v_isLambda_3253_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_mkForall(v_n_3260_, v_bi_3262_, v_ty_3263_, v_b_3258_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_mkLambda(v_n_3260_, v_bi_3262_, v_ty_3263_, v_b_3258_);
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3289_, lean_object* v_lctx_3290_, lean_object* v___x_3291_, lean_object* v_isLambda_3292_, lean_object* v_usedLetOnly_3293_, lean_object* v_generalizeNondepLet_3294_, lean_object* v_i_3295_, lean_object* v_x_3296_, lean_object* v_b_3297_){
_start:
{
uint8_t v_isLambda_boxed_3298_; uint8_t v_usedLetOnly_boxed_3299_; uint8_t v_generalizeNondepLet_boxed_3300_; lean_object* v_res_3301_; 
v_isLambda_boxed_3298_ = lean_unbox(v_isLambda_3292_);
v_usedLetOnly_boxed_3299_ = lean_unbox(v_usedLetOnly_3293_);
v_generalizeNondepLet_boxed_3300_ = lean_unbox(v_generalizeNondepLet_3294_);
v_res_3301_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3289_, v_lctx_3290_, v___x_3291_, v_isLambda_boxed_3298_, v_usedLetOnly_boxed_3299_, v_generalizeNondepLet_boxed_3300_, v_i_3295_, v_x_3296_, v_b_3297_);
lean_dec(v_i_3295_);
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_xs_3289_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3302_, lean_object* v_lctx_3303_, lean_object* v_xs_3304_, lean_object* v_b_3305_, uint8_t v_usedLetOnly_3306_, uint8_t v_generalizeNondepLet_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___f_3312_; lean_object* v_b_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3308_ = l_Lean_instInhabitedExpr;
v___x_3309_ = lean_box(v_isLambda_3302_);
v___x_3310_ = lean_box(v_usedLetOnly_3306_);
v___x_3311_ = lean_box(v_generalizeNondepLet_3307_);
lean_inc_ref(v_xs_3304_);
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3312_, 0, v_xs_3304_);
lean_closure_set(v___f_3312_, 1, v_lctx_3303_);
lean_closure_set(v___f_3312_, 2, v___x_3308_);
lean_closure_set(v___f_3312_, 3, v___x_3309_);
lean_closure_set(v___f_3312_, 4, v___x_3310_);
lean_closure_set(v___f_3312_, 5, v___x_3311_);
v_b_3313_ = lean_expr_abstract(v_b_3305_, v_xs_3304_);
v___x_3314_ = lean_array_get_size(v_xs_3304_);
lean_dec_ref(v_xs_3304_);
v___x_3315_ = l_Nat_foldRev___redArg(v___x_3314_, v___f_3312_, v_b_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3316_, lean_object* v_lctx_3317_, lean_object* v_xs_3318_, lean_object* v_b_3319_, lean_object* v_usedLetOnly_3320_, lean_object* v_generalizeNondepLet_3321_){
_start:
{
uint8_t v_isLambda_boxed_3322_; uint8_t v_usedLetOnly_boxed_3323_; uint8_t v_generalizeNondepLet_boxed_3324_; lean_object* v_res_3325_; 
v_isLambda_boxed_3322_ = lean_unbox(v_isLambda_3316_);
v_usedLetOnly_boxed_3323_ = lean_unbox(v_usedLetOnly_3320_);
v_generalizeNondepLet_boxed_3324_ = lean_unbox(v_generalizeNondepLet_3321_);
v_res_3325_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3322_, v_lctx_3317_, v_xs_3318_, v_b_3319_, v_usedLetOnly_boxed_3323_, v_generalizeNondepLet_boxed_3324_);
lean_dec_ref(v_b_3319_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3326_, lean_object* v_lctx_3327_, uint8_t v_usedLetOnly_3328_, uint8_t v_generalizeNondepLet_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_zero_3332_; uint8_t v_isZero_3333_; 
v_zero_3332_ = lean_unsigned_to_nat(0u);
v_isZero_3333_ = lean_nat_dec_eq(v_x_3330_, v_zero_3332_);
if (v_isZero_3333_ == 1)
{
lean_dec(v_x_3330_);
lean_dec_ref(v_lctx_3327_);
return v_x_3331_;
}
else
{
lean_object* v_one_3334_; lean_object* v_n_3335_; lean_object* v_n_3337_; lean_object* v_ty_3338_; uint8_t v_bi_3339_; lean_object* v_x_3343_; lean_object* v___x_3344_; 
v_one_3334_ = lean_unsigned_to_nat(1u);
v_n_3335_ = lean_nat_sub(v_x_3330_, v_one_3334_);
lean_dec(v_x_3330_);
v_x_3343_ = lean_array_fget_borrowed(v_xs_3326_, v_n_3335_);
lean_inc_ref(v_lctx_3327_);
v___x_3344_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3327_, v_x_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref(v_x_3331_);
v___x_3345_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3346_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3345_);
v_x_3330_ = v_n_3335_;
v_x_3331_ = v___x_3346_;
goto _start;
}
else
{
lean_object* v_val_3348_; 
v_val_3348_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v___x_3344_, 1);
if (lean_obj_tag(v_val_3348_) == 0)
{
lean_object* v_userName_3349_; lean_object* v_type_3350_; uint8_t v_bi_3351_; 
v_userName_3349_ = lean_ctor_get(v_val_3348_, 2);
lean_inc(v_userName_3349_);
v_type_3350_ = lean_ctor_get(v_val_3348_, 3);
lean_inc_ref(v_type_3350_);
v_bi_3351_ = lean_ctor_get_uint8(v_val_3348_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3348_, 4);
v_n_3337_ = v_userName_3349_;
v_ty_3338_ = v_type_3350_;
v_bi_3339_ = v_bi_3351_;
goto v___jp_3336_;
}
else
{
lean_object* v_userName_3352_; lean_object* v_type_3353_; lean_object* v_value_3354_; uint8_t v_nondep_3355_; uint8_t v___y_3362_; 
v_userName_3352_ = lean_ctor_get(v_val_3348_, 2);
lean_inc(v_userName_3352_);
v_type_3353_ = lean_ctor_get(v_val_3348_, 3);
lean_inc_ref(v_type_3353_);
v_value_3354_ = lean_ctor_get(v_val_3348_, 4);
lean_inc_ref(v_value_3354_);
v_nondep_3355_ = lean_ctor_get_uint8(v_val_3348_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3348_, 5);
if (v_nondep_3355_ == 0)
{
v___y_3362_ = v_nondep_3355_;
goto v___jp_3361_;
}
else
{
if (v_generalizeNondepLet_3329_ == 0)
{
v___y_3362_ = v_generalizeNondepLet_3329_;
goto v___jp_3361_;
}
else
{
uint8_t v___x_3366_; 
lean_dec_ref(v_value_3354_);
v___x_3366_ = 0;
v_n_3337_ = v_userName_3352_;
v_ty_3338_ = v_type_3353_;
v_bi_3339_ = v___x_3366_;
goto v___jp_3336_;
}
}
v___jp_3356_:
{
lean_object* v_ty_3357_; lean_object* v_val_3358_; lean_object* v___x_3359_; 
v_ty_3357_ = lean_expr_abstract_range(v_type_3353_, v_n_3335_, v_xs_3326_);
lean_dec_ref(v_type_3353_);
v_val_3358_ = lean_expr_abstract_range(v_value_3354_, v_n_3335_, v_xs_3326_);
lean_dec_ref(v_value_3354_);
v___x_3359_ = l_Lean_Expr_letE___override(v_userName_3352_, v_ty_3357_, v_val_3358_, v_x_3331_, v_nondep_3355_);
v_x_3330_ = v_n_3335_;
v_x_3331_ = v___x_3359_;
goto _start;
}
v___jp_3361_:
{
if (v_usedLetOnly_3328_ == 0)
{
goto v___jp_3356_;
}
else
{
if (v___y_3362_ == 0)
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_expr_has_loose_bvar(v_x_3331_, v_zero_3332_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v_value_3354_);
lean_dec_ref(v_type_3353_);
lean_dec(v_userName_3352_);
v___x_3364_ = lean_expr_lower_loose_bvars(v_x_3331_, v_one_3334_, v_one_3334_);
lean_dec_ref(v_x_3331_);
v_x_3330_ = v_n_3335_;
v_x_3331_ = v___x_3364_;
goto _start;
}
else
{
goto v___jp_3356_;
}
}
else
{
goto v___jp_3356_;
}
}
}
}
}
v___jp_3336_:
{
lean_object* v_ty_3340_; lean_object* v___x_3341_; 
v_ty_3340_ = lean_expr_abstract_range(v_ty_3338_, v_n_3335_, v_xs_3326_);
lean_dec_ref(v_ty_3338_);
v___x_3341_ = l_Lean_mkLambda(v_n_3337_, v_bi_3339_, v_ty_3340_, v_x_3331_);
v_x_3330_ = v_n_3335_;
v_x_3331_ = v___x_3341_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3367_, lean_object* v_lctx_3368_, lean_object* v_usedLetOnly_3369_, lean_object* v_generalizeNondepLet_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_){
_start:
{
uint8_t v_usedLetOnly_boxed_3373_; uint8_t v_generalizeNondepLet_boxed_3374_; lean_object* v_res_3375_; 
v_usedLetOnly_boxed_3373_ = lean_unbox(v_usedLetOnly_3369_);
v_generalizeNondepLet_boxed_3374_ = lean_unbox(v_generalizeNondepLet_3370_);
v_res_3375_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3367_, v_lctx_3368_, v_usedLetOnly_boxed_3373_, v_generalizeNondepLet_boxed_3374_, v_x_3371_, v_x_3372_);
lean_dec_ref(v_xs_3367_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3376_, lean_object* v_lctx_3377_, uint8_t v_usedLetOnly_3378_, uint8_t v_generalizeNondepLet_3379_, lean_object* v_x_3380_, lean_object* v_x_3381_){
_start:
{
lean_object* v_zero_3382_; uint8_t v_isZero_3383_; 
v_zero_3382_ = lean_unsigned_to_nat(0u);
v_isZero_3383_ = lean_nat_dec_eq(v_x_3380_, v_zero_3382_);
if (v_isZero_3383_ == 1)
{
lean_dec_ref(v_lctx_3377_);
return v_x_3381_;
}
else
{
lean_object* v_one_3384_; lean_object* v_n_3385_; lean_object* v_n_3387_; lean_object* v_ty_3388_; uint8_t v_bi_3389_; lean_object* v_x_3393_; lean_object* v___x_3394_; 
v_one_3384_ = lean_unsigned_to_nat(1u);
v_n_3385_ = lean_nat_sub(v_x_3380_, v_one_3384_);
v_x_3393_ = lean_array_fget_borrowed(v_xs_3376_, v_n_3385_);
lean_inc_ref(v_lctx_3377_);
v___x_3394_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3377_, v_x_3393_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec_ref(v_x_3381_);
v___x_3395_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3396_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3395_);
v___x_3397_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3376_, v_lctx_3377_, v_usedLetOnly_3378_, v_generalizeNondepLet_3379_, v_n_3385_, v___x_3396_);
return v___x_3397_;
}
else
{
lean_object* v_val_3398_; 
v_val_3398_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v___x_3394_, 1);
if (lean_obj_tag(v_val_3398_) == 0)
{
lean_object* v_userName_3399_; lean_object* v_type_3400_; uint8_t v_bi_3401_; 
v_userName_3399_ = lean_ctor_get(v_val_3398_, 2);
lean_inc(v_userName_3399_);
v_type_3400_ = lean_ctor_get(v_val_3398_, 3);
lean_inc_ref(v_type_3400_);
v_bi_3401_ = lean_ctor_get_uint8(v_val_3398_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3398_, 4);
v_n_3387_ = v_userName_3399_;
v_ty_3388_ = v_type_3400_;
v_bi_3389_ = v_bi_3401_;
goto v___jp_3386_;
}
else
{
lean_object* v_userName_3402_; lean_object* v_type_3403_; lean_object* v_value_3404_; uint8_t v_nondep_3405_; uint8_t v___y_3412_; 
v_userName_3402_ = lean_ctor_get(v_val_3398_, 2);
lean_inc(v_userName_3402_);
v_type_3403_ = lean_ctor_get(v_val_3398_, 3);
lean_inc_ref(v_type_3403_);
v_value_3404_ = lean_ctor_get(v_val_3398_, 4);
lean_inc_ref(v_value_3404_);
v_nondep_3405_ = lean_ctor_get_uint8(v_val_3398_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3398_, 5);
if (v_nondep_3405_ == 0)
{
v___y_3412_ = v_nondep_3405_;
goto v___jp_3411_;
}
else
{
if (v_generalizeNondepLet_3379_ == 0)
{
v___y_3412_ = v_generalizeNondepLet_3379_;
goto v___jp_3411_;
}
else
{
uint8_t v___x_3416_; 
lean_dec_ref(v_value_3404_);
v___x_3416_ = 0;
v_n_3387_ = v_userName_3402_;
v_ty_3388_ = v_type_3403_;
v_bi_3389_ = v___x_3416_;
goto v___jp_3386_;
}
}
v___jp_3406_:
{
lean_object* v_ty_3407_; lean_object* v_val_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_ty_3407_ = lean_expr_abstract_range(v_type_3403_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_type_3403_);
v_val_3408_ = lean_expr_abstract_range(v_value_3404_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_value_3404_);
v___x_3409_ = l_Lean_Expr_letE___override(v_userName_3402_, v_ty_3407_, v_val_3408_, v_x_3381_, v_nondep_3405_);
v___x_3410_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3376_, v_lctx_3377_, v_usedLetOnly_3378_, v_generalizeNondepLet_3379_, v_n_3385_, v___x_3409_);
return v___x_3410_;
}
v___jp_3411_:
{
if (v_usedLetOnly_3378_ == 0)
{
goto v___jp_3406_;
}
else
{
if (v___y_3412_ == 0)
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_expr_has_loose_bvar(v_x_3381_, v_zero_3382_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec_ref(v_value_3404_);
lean_dec_ref(v_type_3403_);
lean_dec(v_userName_3402_);
v___x_3414_ = lean_expr_lower_loose_bvars(v_x_3381_, v_one_3384_, v_one_3384_);
lean_dec_ref(v_x_3381_);
v___x_3415_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3376_, v_lctx_3377_, v_usedLetOnly_3378_, v_generalizeNondepLet_3379_, v_n_3385_, v___x_3414_);
return v___x_3415_;
}
else
{
goto v___jp_3406_;
}
}
else
{
goto v___jp_3406_;
}
}
}
}
}
v___jp_3386_:
{
lean_object* v_ty_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v_ty_3390_ = lean_expr_abstract_range(v_ty_3388_, v_n_3385_, v_xs_3376_);
lean_dec_ref(v_ty_3388_);
v___x_3391_ = l_Lean_mkLambda(v_n_3387_, v_bi_3389_, v_ty_3390_, v_x_3381_);
v___x_3392_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3376_, v_lctx_3377_, v_usedLetOnly_3378_, v_generalizeNondepLet_3379_, v_n_3385_, v___x_3391_);
return v___x_3392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3417_, lean_object* v_lctx_3418_, lean_object* v_usedLetOnly_3419_, lean_object* v_generalizeNondepLet_3420_, lean_object* v_x_3421_, lean_object* v_x_3422_){
_start:
{
uint8_t v_usedLetOnly_boxed_3423_; uint8_t v_generalizeNondepLet_boxed_3424_; lean_object* v_res_3425_; 
v_usedLetOnly_boxed_3423_ = lean_unbox(v_usedLetOnly_3419_);
v_generalizeNondepLet_boxed_3424_ = lean_unbox(v_generalizeNondepLet_3420_);
v_res_3425_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3417_, v_lctx_3418_, v_usedLetOnly_boxed_3423_, v_generalizeNondepLet_boxed_3424_, v_x_3421_, v_x_3422_);
lean_dec(v_x_3421_);
lean_dec_ref(v_xs_3417_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3426_, lean_object* v_xs_3427_, lean_object* v_b_3428_, uint8_t v_usedLetOnly_3429_, uint8_t v_generalizeNondepLet_3430_){
_start:
{
lean_object* v_b_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_b_3431_ = lean_expr_abstract(v_b_3428_, v_xs_3427_);
v___x_3432_ = lean_array_get_size(v_xs_3427_);
v___x_3433_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3427_, v_lctx_3426_, v_usedLetOnly_3429_, v_generalizeNondepLet_3430_, v___x_3432_, v_b_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3434_, lean_object* v_xs_3435_, lean_object* v_b_3436_, lean_object* v_usedLetOnly_3437_, lean_object* v_generalizeNondepLet_3438_){
_start:
{
uint8_t v_usedLetOnly_boxed_3439_; uint8_t v_generalizeNondepLet_boxed_3440_; lean_object* v_res_3441_; 
v_usedLetOnly_boxed_3439_ = lean_unbox(v_usedLetOnly_3437_);
v_generalizeNondepLet_boxed_3440_ = lean_unbox(v_generalizeNondepLet_3438_);
v_res_3441_ = l_Lean_LocalContext_mkLambda(v_lctx_3434_, v_xs_3435_, v_b_3436_, v_usedLetOnly_boxed_3439_, v_generalizeNondepLet_boxed_3440_);
lean_dec_ref(v_b_3436_);
lean_dec_ref(v_xs_3435_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3442_, lean_object* v_lctx_3443_, uint8_t v_usedLetOnly_3444_, uint8_t v_generalizeNondepLet_3445_, lean_object* v_x_3446_, lean_object* v_x_3447_){
_start:
{
lean_object* v_zero_3448_; uint8_t v_isZero_3449_; 
v_zero_3448_ = lean_unsigned_to_nat(0u);
v_isZero_3449_ = lean_nat_dec_eq(v_x_3446_, v_zero_3448_);
if (v_isZero_3449_ == 1)
{
lean_dec(v_x_3446_);
lean_dec_ref(v_lctx_3443_);
return v_x_3447_;
}
else
{
lean_object* v_one_3450_; lean_object* v_n_3451_; lean_object* v_n_3453_; lean_object* v_ty_3454_; uint8_t v_bi_3455_; lean_object* v_x_3459_; lean_object* v___x_3460_; 
v_one_3450_ = lean_unsigned_to_nat(1u);
v_n_3451_ = lean_nat_sub(v_x_3446_, v_one_3450_);
lean_dec(v_x_3446_);
v_x_3459_ = lean_array_fget_borrowed(v_xs_3442_, v_n_3451_);
lean_inc_ref(v_lctx_3443_);
v___x_3460_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3443_, v_x_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref(v_x_3447_);
v___x_3461_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3462_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3461_);
v_x_3446_ = v_n_3451_;
v_x_3447_ = v___x_3462_;
goto _start;
}
else
{
lean_object* v_val_3464_; 
v_val_3464_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_val_3464_);
lean_dec_ref_known(v___x_3460_, 1);
if (lean_obj_tag(v_val_3464_) == 0)
{
lean_object* v_userName_3465_; lean_object* v_type_3466_; uint8_t v_bi_3467_; 
v_userName_3465_ = lean_ctor_get(v_val_3464_, 2);
lean_inc(v_userName_3465_);
v_type_3466_ = lean_ctor_get(v_val_3464_, 3);
lean_inc_ref(v_type_3466_);
v_bi_3467_ = lean_ctor_get_uint8(v_val_3464_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3464_, 4);
v_n_3453_ = v_userName_3465_;
v_ty_3454_ = v_type_3466_;
v_bi_3455_ = v_bi_3467_;
goto v___jp_3452_;
}
else
{
lean_object* v_userName_3468_; lean_object* v_type_3469_; lean_object* v_value_3470_; uint8_t v_nondep_3471_; uint8_t v___y_3478_; 
v_userName_3468_ = lean_ctor_get(v_val_3464_, 2);
lean_inc(v_userName_3468_);
v_type_3469_ = lean_ctor_get(v_val_3464_, 3);
lean_inc_ref(v_type_3469_);
v_value_3470_ = lean_ctor_get(v_val_3464_, 4);
lean_inc_ref(v_value_3470_);
v_nondep_3471_ = lean_ctor_get_uint8(v_val_3464_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3464_, 5);
if (v_nondep_3471_ == 0)
{
v___y_3478_ = v_nondep_3471_;
goto v___jp_3477_;
}
else
{
if (v_generalizeNondepLet_3445_ == 0)
{
v___y_3478_ = v_generalizeNondepLet_3445_;
goto v___jp_3477_;
}
else
{
uint8_t v___x_3482_; 
lean_dec_ref(v_value_3470_);
v___x_3482_ = 0;
v_n_3453_ = v_userName_3468_;
v_ty_3454_ = v_type_3469_;
v_bi_3455_ = v___x_3482_;
goto v___jp_3452_;
}
}
v___jp_3472_:
{
lean_object* v_ty_3473_; lean_object* v_val_3474_; lean_object* v___x_3475_; 
v_ty_3473_ = lean_expr_abstract_range(v_type_3469_, v_n_3451_, v_xs_3442_);
lean_dec_ref(v_type_3469_);
v_val_3474_ = lean_expr_abstract_range(v_value_3470_, v_n_3451_, v_xs_3442_);
lean_dec_ref(v_value_3470_);
v___x_3475_ = l_Lean_Expr_letE___override(v_userName_3468_, v_ty_3473_, v_val_3474_, v_x_3447_, v_nondep_3471_);
v_x_3446_ = v_n_3451_;
v_x_3447_ = v___x_3475_;
goto _start;
}
v___jp_3477_:
{
if (v_usedLetOnly_3444_ == 0)
{
goto v___jp_3472_;
}
else
{
if (v___y_3478_ == 0)
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_expr_has_loose_bvar(v_x_3447_, v_zero_3448_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref(v_value_3470_);
lean_dec_ref(v_type_3469_);
lean_dec(v_userName_3468_);
v___x_3480_ = lean_expr_lower_loose_bvars(v_x_3447_, v_one_3450_, v_one_3450_);
lean_dec_ref(v_x_3447_);
v_x_3446_ = v_n_3451_;
v_x_3447_ = v___x_3480_;
goto _start;
}
else
{
goto v___jp_3472_;
}
}
else
{
goto v___jp_3472_;
}
}
}
}
}
v___jp_3452_:
{
lean_object* v_ty_3456_; lean_object* v___x_3457_; 
v_ty_3456_ = lean_expr_abstract_range(v_ty_3454_, v_n_3451_, v_xs_3442_);
lean_dec_ref(v_ty_3454_);
v___x_3457_ = l_Lean_mkForall(v_n_3453_, v_bi_3455_, v_ty_3456_, v_x_3447_);
v_x_3446_ = v_n_3451_;
v_x_3447_ = v___x_3457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3483_, lean_object* v_lctx_3484_, lean_object* v_usedLetOnly_3485_, lean_object* v_generalizeNondepLet_3486_, lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
uint8_t v_usedLetOnly_boxed_3489_; uint8_t v_generalizeNondepLet_boxed_3490_; lean_object* v_res_3491_; 
v_usedLetOnly_boxed_3489_ = lean_unbox(v_usedLetOnly_3485_);
v_generalizeNondepLet_boxed_3490_ = lean_unbox(v_generalizeNondepLet_3486_);
v_res_3491_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3483_, v_lctx_3484_, v_usedLetOnly_boxed_3489_, v_generalizeNondepLet_boxed_3490_, v_x_3487_, v_x_3488_);
lean_dec_ref(v_xs_3483_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3492_, lean_object* v_lctx_3493_, uint8_t v_usedLetOnly_3494_, uint8_t v_generalizeNondepLet_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_){
_start:
{
lean_object* v_zero_3498_; uint8_t v_isZero_3499_; 
v_zero_3498_ = lean_unsigned_to_nat(0u);
v_isZero_3499_ = lean_nat_dec_eq(v_x_3496_, v_zero_3498_);
if (v_isZero_3499_ == 1)
{
lean_dec_ref(v_lctx_3493_);
return v_x_3497_;
}
else
{
lean_object* v_one_3500_; lean_object* v_n_3501_; lean_object* v_n_3503_; lean_object* v_ty_3504_; uint8_t v_bi_3505_; lean_object* v_x_3509_; lean_object* v___x_3510_; 
v_one_3500_ = lean_unsigned_to_nat(1u);
v_n_3501_ = lean_nat_sub(v_x_3496_, v_one_3500_);
v_x_3509_ = lean_array_fget_borrowed(v_xs_3492_, v_n_3501_);
lean_inc_ref(v_lctx_3493_);
v___x_3510_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3493_, v_x_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec_ref(v_x_3497_);
v___x_3511_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3512_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3511_);
v___x_3513_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3492_, v_lctx_3493_, v_usedLetOnly_3494_, v_generalizeNondepLet_3495_, v_n_3501_, v___x_3512_);
return v___x_3513_;
}
else
{
lean_object* v_val_3514_; 
v_val_3514_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v___x_3510_, 1);
if (lean_obj_tag(v_val_3514_) == 0)
{
lean_object* v_userName_3515_; lean_object* v_type_3516_; uint8_t v_bi_3517_; 
v_userName_3515_ = lean_ctor_get(v_val_3514_, 2);
lean_inc(v_userName_3515_);
v_type_3516_ = lean_ctor_get(v_val_3514_, 3);
lean_inc_ref(v_type_3516_);
v_bi_3517_ = lean_ctor_get_uint8(v_val_3514_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3514_, 4);
v_n_3503_ = v_userName_3515_;
v_ty_3504_ = v_type_3516_;
v_bi_3505_ = v_bi_3517_;
goto v___jp_3502_;
}
else
{
lean_object* v_userName_3518_; lean_object* v_type_3519_; lean_object* v_value_3520_; uint8_t v_nondep_3521_; uint8_t v___y_3528_; 
v_userName_3518_ = lean_ctor_get(v_val_3514_, 2);
lean_inc(v_userName_3518_);
v_type_3519_ = lean_ctor_get(v_val_3514_, 3);
lean_inc_ref(v_type_3519_);
v_value_3520_ = lean_ctor_get(v_val_3514_, 4);
lean_inc_ref(v_value_3520_);
v_nondep_3521_ = lean_ctor_get_uint8(v_val_3514_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3514_, 5);
if (v_nondep_3521_ == 0)
{
v___y_3528_ = v_nondep_3521_;
goto v___jp_3527_;
}
else
{
if (v_generalizeNondepLet_3495_ == 0)
{
v___y_3528_ = v_generalizeNondepLet_3495_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3532_; 
lean_dec_ref(v_value_3520_);
v___x_3532_ = 0;
v_n_3503_ = v_userName_3518_;
v_ty_3504_ = v_type_3519_;
v_bi_3505_ = v___x_3532_;
goto v___jp_3502_;
}
}
v___jp_3522_:
{
lean_object* v_ty_3523_; lean_object* v_val_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_ty_3523_ = lean_expr_abstract_range(v_type_3519_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_type_3519_);
v_val_3524_ = lean_expr_abstract_range(v_value_3520_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_value_3520_);
v___x_3525_ = l_Lean_Expr_letE___override(v_userName_3518_, v_ty_3523_, v_val_3524_, v_x_3497_, v_nondep_3521_);
v___x_3526_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3492_, v_lctx_3493_, v_usedLetOnly_3494_, v_generalizeNondepLet_3495_, v_n_3501_, v___x_3525_);
return v___x_3526_;
}
v___jp_3527_:
{
if (v_usedLetOnly_3494_ == 0)
{
goto v___jp_3522_;
}
else
{
if (v___y_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = lean_expr_has_loose_bvar(v_x_3497_, v_zero_3498_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v_value_3520_);
lean_dec_ref(v_type_3519_);
lean_dec(v_userName_3518_);
v___x_3530_ = lean_expr_lower_loose_bvars(v_x_3497_, v_one_3500_, v_one_3500_);
lean_dec_ref(v_x_3497_);
v___x_3531_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3492_, v_lctx_3493_, v_usedLetOnly_3494_, v_generalizeNondepLet_3495_, v_n_3501_, v___x_3530_);
return v___x_3531_;
}
else
{
goto v___jp_3522_;
}
}
else
{
goto v___jp_3522_;
}
}
}
}
}
v___jp_3502_:
{
lean_object* v_ty_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v_ty_3506_ = lean_expr_abstract_range(v_ty_3504_, v_n_3501_, v_xs_3492_);
lean_dec_ref(v_ty_3504_);
v___x_3507_ = l_Lean_mkForall(v_n_3503_, v_bi_3505_, v_ty_3506_, v_x_3497_);
v___x_3508_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3492_, v_lctx_3493_, v_usedLetOnly_3494_, v_generalizeNondepLet_3495_, v_n_3501_, v___x_3507_);
return v___x_3508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3533_, lean_object* v_lctx_3534_, lean_object* v_usedLetOnly_3535_, lean_object* v_generalizeNondepLet_3536_, lean_object* v_x_3537_, lean_object* v_x_3538_){
_start:
{
uint8_t v_usedLetOnly_boxed_3539_; uint8_t v_generalizeNondepLet_boxed_3540_; lean_object* v_res_3541_; 
v_usedLetOnly_boxed_3539_ = lean_unbox(v_usedLetOnly_3535_);
v_generalizeNondepLet_boxed_3540_ = lean_unbox(v_generalizeNondepLet_3536_);
v_res_3541_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3533_, v_lctx_3534_, v_usedLetOnly_boxed_3539_, v_generalizeNondepLet_boxed_3540_, v_x_3537_, v_x_3538_);
lean_dec(v_x_3537_);
lean_dec_ref(v_xs_3533_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3542_, lean_object* v_xs_3543_, lean_object* v_b_3544_, uint8_t v_usedLetOnly_3545_, uint8_t v_generalizeNondepLet_3546_){
_start:
{
lean_object* v_b_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_b_3547_ = lean_expr_abstract(v_b_3544_, v_xs_3543_);
v___x_3548_ = lean_array_get_size(v_xs_3543_);
v___x_3549_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3543_, v_lctx_3542_, v_usedLetOnly_3545_, v_generalizeNondepLet_3546_, v___x_3548_, v_b_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3550_, lean_object* v_xs_3551_, lean_object* v_b_3552_, lean_object* v_usedLetOnly_3553_, lean_object* v_generalizeNondepLet_3554_){
_start:
{
uint8_t v_usedLetOnly_boxed_3555_; uint8_t v_generalizeNondepLet_boxed_3556_; lean_object* v_res_3557_; 
v_usedLetOnly_boxed_3555_ = lean_unbox(v_usedLetOnly_3553_);
v_generalizeNondepLet_boxed_3556_ = lean_unbox(v_generalizeNondepLet_3554_);
v_res_3557_ = l_Lean_LocalContext_mkForall(v_lctx_3550_, v_xs_3551_, v_b_3552_, v_usedLetOnly_boxed_3555_, v_generalizeNondepLet_boxed_3556_);
lean_dec_ref(v_b_3552_);
lean_dec_ref(v_xs_3551_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3558_, lean_object* v_p_3559_, lean_object* v_d_3560_){
_start:
{
if (lean_obj_tag(v_d_3560_) == 0)
{
uint8_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v_p_3559_);
v___x_3561_ = 0;
v___x_3562_ = lean_box(v___x_3561_);
v___x_3563_ = lean_apply_2(v_toPure_3558_, lean_box(0), v___x_3562_);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; lean_object* v___x_3565_; 
lean_dec(v_toPure_3558_);
v_val_3564_ = lean_ctor_get(v_d_3560_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v_d_3560_, 1);
v___x_3565_ = lean_apply_1(v_p_3559_, v_val_3564_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3566_, lean_object* v_lctx_3567_, lean_object* v_p_3568_){
_start:
{
lean_object* v_toApplicative_3569_; lean_object* v_decls_3570_; lean_object* v_toPure_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; 
v_toApplicative_3569_ = lean_ctor_get(v_inst_3566_, 0);
v_decls_3570_ = lean_ctor_get(v_lctx_3567_, 1);
lean_inc_ref(v_decls_3570_);
lean_dec_ref(v_lctx_3567_);
v_toPure_3571_ = lean_ctor_get(v_toApplicative_3569_, 1);
lean_inc(v_toPure_3571_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3572_, 0, v_toPure_3571_);
lean_closure_set(v___f_3572_, 1, v_p_3568_);
v___x_3573_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3566_, v_decls_3570_, v___f_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3574_, lean_object* v_inst_3575_, lean_object* v_lctx_3576_, lean_object* v_p_3577_){
_start:
{
lean_object* v_toApplicative_3578_; lean_object* v_decls_3579_; lean_object* v_toPure_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; 
v_toApplicative_3578_ = lean_ctor_get(v_inst_3575_, 0);
v_decls_3579_ = lean_ctor_get(v_lctx_3576_, 1);
lean_inc_ref(v_decls_3579_);
lean_dec_ref(v_lctx_3576_);
v_toPure_3580_ = lean_ctor_get(v_toApplicative_3578_, 1);
lean_inc(v_toPure_3580_);
v___f_3581_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3581_, 0, v_toPure_3580_);
lean_closure_set(v___f_3581_, 1, v_p_3577_);
v___x_3582_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3575_, v_decls_3579_, v___f_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3583_, uint8_t v_b_3584_){
_start:
{
if (v_b_3584_ == 0)
{
uint8_t v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = 1;
v___x_3586_ = lean_box(v___x_3585_);
v___x_3587_ = lean_apply_2(v_toPure_3583_, lean_box(0), v___x_3586_);
return v___x_3587_;
}
else
{
uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = 0;
v___x_3589_ = lean_box(v___x_3588_);
v___x_3590_ = lean_apply_2(v_toPure_3583_, lean_box(0), v___x_3589_);
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3591_, lean_object* v_b_3592_){
_start:
{
uint8_t v_b_boxed_3593_; lean_object* v_res_3594_; 
v_b_boxed_3593_ = lean_unbox(v_b_3592_);
v_res_3594_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3591_, v_b_boxed_3593_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3595_, lean_object* v_toBind_3596_, lean_object* v___f_3597_, lean_object* v_p_3598_, lean_object* v_v_3599_){
_start:
{
if (lean_obj_tag(v_v_3599_) == 0)
{
uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec(v_p_3598_);
v___x_3600_ = 1;
v___x_3601_ = lean_box(v___x_3600_);
v___x_3602_ = lean_apply_2(v_toPure_3595_, lean_box(0), v___x_3601_);
v___x_3603_ = lean_apply_4(v_toBind_3596_, lean_box(0), lean_box(0), v___x_3602_, v___f_3597_);
return v___x_3603_;
}
else
{
lean_object* v_val_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v_toPure_3595_);
v_val_3604_ = lean_ctor_get(v_v_3599_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v_v_3599_, 1);
v___x_3605_ = lean_apply_1(v_p_3598_, v_val_3604_);
v___x_3606_ = lean_apply_4(v_toBind_3596_, lean_box(0), lean_box(0), v___x_3605_, v___f_3597_);
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3607_, lean_object* v_lctx_3608_, lean_object* v_p_3609_){
_start:
{
lean_object* v_toApplicative_3610_; lean_object* v_decls_3611_; lean_object* v_toBind_3612_; lean_object* v_toPure_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_toApplicative_3610_ = lean_ctor_get(v_inst_3607_, 0);
v_decls_3611_ = lean_ctor_get(v_lctx_3608_, 1);
lean_inc_ref(v_decls_3611_);
lean_dec_ref(v_lctx_3608_);
v_toBind_3612_ = lean_ctor_get(v_inst_3607_, 1);
lean_inc_n(v_toBind_3612_, 2);
v_toPure_3613_ = lean_ctor_get(v_toApplicative_3610_, 1);
lean_inc_n(v_toPure_3613_, 2);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3614_, 0, v_toPure_3613_);
lean_inc_ref(v___f_3614_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3615_, 0, v_toPure_3613_);
lean_closure_set(v___f_3615_, 1, v_toBind_3612_);
lean_closure_set(v___f_3615_, 2, v___f_3614_);
lean_closure_set(v___f_3615_, 3, v_p_3609_);
v___x_3616_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3607_, v_decls_3611_, v___f_3615_);
v___x_3617_ = lean_apply_4(v_toBind_3612_, lean_box(0), lean_box(0), v___x_3616_, v___f_3614_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3618_, lean_object* v_inst_3619_, lean_object* v_lctx_3620_, lean_object* v_p_3621_){
_start:
{
lean_object* v_toApplicative_3622_; lean_object* v_decls_3623_; lean_object* v_toBind_3624_; lean_object* v_toPure_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_toApplicative_3622_ = lean_ctor_get(v_inst_3619_, 0);
v_decls_3623_ = lean_ctor_get(v_lctx_3620_, 1);
lean_inc_ref(v_decls_3623_);
lean_dec_ref(v_lctx_3620_);
v_toBind_3624_ = lean_ctor_get(v_inst_3619_, 1);
lean_inc_n(v_toBind_3624_, 2);
v_toPure_3625_ = lean_ctor_get(v_toApplicative_3622_, 1);
lean_inc_n(v_toPure_3625_, 2);
v___f_3626_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3626_, 0, v_toPure_3625_);
lean_inc_ref(v___f_3626_);
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3627_, 0, v_toPure_3625_);
lean_closure_set(v___f_3627_, 1, v_toBind_3624_);
lean_closure_set(v___f_3627_, 2, v___f_3626_);
lean_closure_set(v___f_3627_, 3, v_p_3621_);
v___x_3628_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3619_, v_decls_3623_, v___f_3627_);
v___x_3629_ = lean_apply_4(v_toBind_3624_, lean_box(0), lean_box(0), v___x_3628_, v___f_3626_);
return v___x_3629_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3630_, lean_object* v_d_3631_){
_start:
{
if (lean_obj_tag(v_d_3631_) == 0)
{
uint8_t v___x_3632_; 
lean_dec_ref(v_p_3630_);
v___x_3632_ = 0;
return v___x_3632_;
}
else
{
lean_object* v_val_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v_val_3633_ = lean_ctor_get(v_d_3631_, 0);
lean_inc(v_val_3633_);
lean_dec_ref_known(v_d_3631_, 1);
v___x_3634_ = lean_apply_1(v_p_3630_, v_val_3633_);
v___x_3635_ = lean_unbox(v___x_3634_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3636_, lean_object* v_d_3637_){
_start:
{
uint8_t v_res_3638_; lean_object* v_r_3639_; 
v_res_3638_ = l_Lean_LocalContext_any___lam__0(v_p_3636_, v_d_3637_);
v_r_3639_ = lean_box(v_res_3638_);
return v_r_3639_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3640_, lean_object* v_p_3641_){
_start:
{
lean_object* v___x_3642_; lean_object* v_decls_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3642_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3643_ = lean_ctor_get(v_lctx_3640_, 1);
lean_inc_ref(v_decls_3643_);
lean_dec_ref(v_lctx_3640_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3644_, 0, v_p_3641_);
v___x_3645_ = l_Lean_PersistentArray_anyM___redArg(v___x_3642_, v_decls_3643_, v___f_3644_);
v___x_3646_ = lean_unbox(v___x_3645_);
lean_dec(v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3647_, lean_object* v_p_3648_){
_start:
{
uint8_t v_res_3649_; lean_object* v_r_3650_; 
v_res_3649_ = l_Lean_LocalContext_any(v_lctx_3647_, v_p_3648_);
v_r_3650_ = lean_box(v_res_3649_);
return v_r_3650_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3651_, lean_object* v_v_3652_){
_start:
{
if (lean_obj_tag(v_v_3652_) == 0)
{
uint8_t v___x_3653_; 
lean_dec_ref(v_p_3651_);
v___x_3653_ = 0;
return v___x_3653_;
}
else
{
lean_object* v_val_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v_val_3654_ = lean_ctor_get(v_v_3652_, 0);
lean_inc(v_val_3654_);
lean_dec_ref_known(v_v_3652_, 1);
v___x_3655_ = lean_apply_1(v_p_3651_, v_val_3654_);
v___x_3656_ = lean_unbox(v___x_3655_);
if (v___x_3656_ == 0)
{
uint8_t v___x_3657_; 
v___x_3657_ = 1;
return v___x_3657_;
}
else
{
uint8_t v___x_3658_; 
v___x_3658_ = 0;
return v___x_3658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3659_, lean_object* v_v_3660_){
_start:
{
uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_res_3661_ = l_Lean_LocalContext_all___lam__0(v_p_3659_, v_v_3660_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3663_, lean_object* v_p_3664_){
_start:
{
lean_object* v___x_3665_; lean_object* v_decls_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3665_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3666_ = lean_ctor_get(v_lctx_3663_, 1);
lean_inc_ref(v_decls_3666_);
lean_dec_ref(v_lctx_3663_);
v___f_3667_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3667_, 0, v_p_3664_);
v___x_3668_ = l_Lean_PersistentArray_anyM___redArg(v___x_3665_, v_decls_3666_, v___f_3667_);
v___x_3669_ = lean_unbox(v___x_3668_);
lean_dec(v___x_3668_);
if (v___x_3669_ == 0)
{
uint8_t v___x_3670_; 
v___x_3670_ = 1;
return v___x_3670_;
}
else
{
uint8_t v___x_3671_; 
v___x_3671_ = 0;
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3672_, lean_object* v_p_3673_){
_start:
{
uint8_t v_res_3674_; lean_object* v_r_3675_; 
v_res_3674_ = l_Lean_LocalContext_all(v_lctx_3672_, v_p_3673_);
v_r_3675_ = lean_box(v_res_3674_);
return v_r_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3676_, lean_object* v_a_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_zero_3680_; uint8_t v_isZero_3681_; 
v_zero_3680_ = lean_unsigned_to_nat(0u);
v_isZero_3681_ = lean_nat_dec_eq(v_i_3676_, v_zero_3680_);
if (v_isZero_3681_ == 1)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec(v_i_3676_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_a_3677_);
lean_ctor_set(v___x_3682_, 1, v___y_3678_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
lean_ctor_set(v___x_3683_, 1, v___y_3679_);
return v___x_3683_;
}
else
{
lean_object* v_decls_3684_; lean_object* v_size_3685_; lean_object* v___x_3686_; lean_object* v_one_3687_; lean_object* v_n_3688_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3705_; lean_object* v___y_3706_; uint8_t v___y_3707_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3717_; uint8_t v___x_3721_; 
v_decls_3684_ = lean_ctor_get(v_a_3677_, 1);
v_size_3685_ = lean_ctor_get(v_decls_3684_, 2);
v___x_3686_ = lean_box(0);
v_one_3687_ = lean_unsigned_to_nat(1u);
v_n_3688_ = lean_nat_sub(v_i_3676_, v_one_3687_);
lean_dec(v_i_3676_);
v___x_3721_ = lean_nat_dec_lt(v_n_3688_, v_size_3685_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = l_outOfBounds___redArg(v___x_3686_);
v___y_3717_ = v___x_3722_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3686_, v_decls_3684_, v_n_3688_);
v___y_3717_ = v___x_3723_;
goto v___jp_3716_;
}
v___jp_3689_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_LocalContext_setUserName(v_a_3677_, v___y_3693_, v___y_3691_);
v_i_3676_ = v_n_3688_;
v_a_3677_ = v___x_3694_;
v___y_3678_ = v___y_3690_;
v___y_3679_ = v___y_3692_;
goto _start;
}
v___jp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_fst_3701_; lean_object* v_snd_3702_; lean_object* v_fvarId_3703_; 
lean_inc(v___y_3698_);
v___x_3699_ = l_Lean_NameSet_insert(v___y_3678_, v___y_3698_);
v___x_3700_ = l_Lean_sanitizeName(v___y_3698_, v___y_3679_);
v_fst_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_fst_3701_);
v_snd_3702_ = lean_ctor_get(v___x_3700_, 1);
lean_inc(v_snd_3702_);
lean_dec_ref(v___x_3700_);
v_fvarId_3703_ = lean_ctor_get(v___y_3697_, 1);
lean_inc(v_fvarId_3703_);
lean_dec_ref(v___y_3697_);
v___y_3690_ = v___x_3699_;
v___y_3691_ = v_fst_3701_;
v___y_3692_ = v_snd_3702_;
v___y_3693_ = v_fvarId_3703_;
goto v___jp_3689_;
}
v___jp_3704_:
{
if (v___y_3707_ == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v___y_3705_);
v___x_3708_ = l_Lean_NameSet_insert(v___y_3678_, v___y_3706_);
v_i_3676_ = v_n_3688_;
v___y_3678_ = v___x_3708_;
goto _start;
}
else
{
v___y_3697_ = v___y_3705_;
v___y_3698_ = v___y_3706_;
goto v___jp_3696_;
}
}
v___jp_3710_:
{
uint8_t v___x_3713_; 
v___x_3713_ = l_Lean_Name_hasMacroScopes(v___y_3712_);
if (v___x_3713_ == 0)
{
lean_object* v_userName_3714_; uint8_t v___x_3715_; 
v_userName_3714_ = lean_ctor_get(v___y_3711_, 2);
v___x_3715_ = l_Lean_NameSet_contains(v___y_3678_, v_userName_3714_);
v___y_3705_ = v___y_3711_;
v___y_3706_ = v___y_3712_;
v___y_3707_ = v___x_3715_;
goto v___jp_3704_;
}
else
{
v___y_3697_ = v___y_3711_;
v___y_3698_ = v___y_3712_;
goto v___jp_3696_;
}
}
v___jp_3716_:
{
if (lean_obj_tag(v___y_3717_) == 0)
{
v_i_3676_ = v_n_3688_;
goto _start;
}
else
{
lean_object* v_val_3719_; lean_object* v_userName_3720_; 
v_val_3719_ = lean_ctor_get(v___y_3717_, 0);
lean_inc(v_val_3719_);
lean_dec_ref_known(v___y_3717_, 1);
v_userName_3720_ = lean_ctor_get(v_val_3719_, 2);
lean_inc(v_userName_3720_);
v___y_3711_ = v_val_3719_;
v___y_3712_ = v_userName_3720_;
goto v___jp_3710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_options_3726_; uint8_t v___x_3727_; 
v_options_3726_ = lean_ctor_get(v_a_3725_, 0);
v___x_3727_ = l_Lean_getSanitizeNames(v_options_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_lctx_3724_);
lean_ctor_set(v___x_3728_, 1, v_a_3725_);
return v___x_3728_;
}
else
{
lean_object* v_decls_3729_; lean_object* v_size_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_fst_3733_; lean_object* v_snd_3734_; lean_object* v_fst_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_decls_3729_ = lean_ctor_get(v_lctx_3724_, 1);
v_size_3730_ = lean_ctor_get(v_decls_3729_, 2);
lean_inc(v_size_3730_);
v___x_3731_ = l_Lean_NameSet_empty;
v___x_3732_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3730_, v_lctx_3724_, v___x_3731_, v_a_3725_);
v_fst_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_fst_3733_);
v_snd_3734_ = lean_ctor_get(v___x_3732_, 1);
lean_inc(v_snd_3734_);
lean_dec_ref(v___x_3732_);
v_fst_3735_ = lean_ctor_get(v_fst_3733_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_fst_3733_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v_fst_3733_, 1);
lean_dec(v_unused_3743_);
v___x_3737_ = v_fst_3733_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_fst_3735_);
lean_dec(v_fst_3733_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 1, v_snd_3734_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_fst_3735_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_snd_3734_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3744_, lean_object* v_i_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3745_, v_a_3747_, v___y_3748_, v___y_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3751_, lean_object* v_i_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3751_, v_i_3752_, v_a_3753_, v_a_3754_, v___y_3755_, v___y_3756_);
lean_dec(v_n_3751_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3758_, lean_object* v_fvarId_3759_){
_start:
{
lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___x_3772_; 
lean_inc_ref(v_lctx_3758_);
v___x_3772_ = lean_local_ctx_find(v_lctx_3758_, v_fvarId_3759_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; 
lean_dec_ref(v_lctx_3758_);
v___x_3773_ = lean_box(0);
return v___x_3773_;
}
else
{
lean_object* v_val_3774_; lean_object* v___y_3776_; lean_object* v_userName_3781_; 
v_val_3774_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_val_3774_);
lean_dec_ref_known(v___x_3772_, 1);
v_userName_3781_ = lean_ctor_get(v_val_3774_, 2);
lean_inc(v_userName_3781_);
v___y_3776_ = v_userName_3781_;
goto v___jp_3775_;
v___jp_3775_:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3758_, v___y_3776_);
lean_dec_ref(v_lctx_3758_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3778_; 
lean_dec(v___y_3776_);
lean_dec(v_val_3774_);
v___x_3778_ = lean_box(0);
return v___x_3778_;
}
else
{
lean_object* v_val_3779_; lean_object* v_fvarId_3780_; 
v_val_3779_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_val_3779_);
lean_dec_ref_known(v___x_3777_, 1);
v_fvarId_3780_ = lean_ctor_get(v_val_3774_, 1);
lean_inc(v_fvarId_3780_);
lean_dec(v_val_3774_);
v___y_3768_ = v___y_3776_;
v___y_3769_ = v_val_3779_;
v___y_3770_ = v_fvarId_3780_;
goto v___jp_3767_;
}
}
}
v___jp_3760_:
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Lean_instBEqFVarId_beq(v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec(v___y_3762_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; 
lean_dec(v___y_3761_);
v___x_3765_ = lean_box(0);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___y_3761_);
return v___x_3766_;
}
}
v___jp_3767_:
{
lean_object* v_fvarId_3771_; 
v_fvarId_3771_ = lean_ctor_get(v___y_3769_, 1);
lean_inc(v_fvarId_3771_);
lean_dec_ref(v___y_3769_);
v___y_3761_ = v___y_3768_;
v___y_3762_ = v___y_3770_;
v___y_3763_ = v_fvarId_3771_;
goto v___jp_3760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3782_, size_t v_i_3783_, lean_object* v_bs_3784_){
_start:
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_usize_dec_lt(v_i_3783_, v_sz_3782_);
if (v___x_3785_ == 0)
{
return v_bs_3784_;
}
else
{
lean_object* v_v_3786_; lean_object* v_snd_3787_; lean_object* v___x_3788_; lean_object* v_bs_x27_3789_; size_t v___x_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v_v_3786_ = lean_array_uget_borrowed(v_bs_3784_, v_i_3783_);
v_snd_3787_ = lean_ctor_get(v_v_3786_, 1);
lean_inc(v_snd_3787_);
v___x_3788_ = lean_unsigned_to_nat(0u);
v_bs_x27_3789_ = lean_array_uset(v_bs_3784_, v_i_3783_, v___x_3788_);
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3783_, v___x_3790_);
v___x_3792_ = lean_array_uset(v_bs_x27_3789_, v_i_3783_, v_snd_3787_);
v_i_3783_ = v___x_3791_;
v_bs_3784_ = v___x_3792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3794_, lean_object* v_i_3795_, lean_object* v_bs_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3794_);
lean_dec(v_sz_3794_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3795_);
lean_dec(v_i_3795_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3797_, v_i_boxed_3798_, v_bs_3796_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3800_, size_t v_sz_3801_, size_t v_i_3802_, lean_object* v_bs_3803_){
_start:
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_usize_dec_lt(v_i_3802_, v_sz_3801_);
if (v___x_3804_ == 0)
{
return v_bs_3803_;
}
else
{
lean_object* v_fvarIdToDecl_3805_; lean_object* v_v_3806_; lean_object* v___x_3807_; lean_object* v_bs_x27_3808_; lean_object* v___y_3810_; lean_object* v___x_3815_; 
v_fvarIdToDecl_3805_ = lean_ctor_get(v_lctx_3800_, 0);
v_v_3806_ = lean_array_uget(v_bs_3803_, v_i_3802_);
v___x_3807_ = lean_unsigned_to_nat(0u);
v_bs_x27_3808_ = lean_array_uset(v_bs_3803_, v_i_3802_, v___x_3807_);
v___x_3815_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3805_, v_v_3806_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3807_);
lean_ctor_set(v___x_3816_, 1, v_v_3806_);
v___y_3810_ = v___x_3816_;
goto v___jp_3809_;
}
else
{
lean_object* v_val_3817_; lean_object* v_index_3818_; lean_object* v___x_3819_; 
v_val_3817_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_val_3817_);
lean_dec_ref_known(v___x_3815_, 1);
v_index_3818_ = lean_ctor_get(v_val_3817_, 0);
lean_inc(v_index_3818_);
lean_dec(v_val_3817_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_index_3818_);
lean_ctor_set(v___x_3819_, 1, v_v_3806_);
v___y_3810_ = v___x_3819_;
goto v___jp_3809_;
}
v___jp_3809_:
{
size_t v___x_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((size_t)1ULL);
v___x_3812_ = lean_usize_add(v_i_3802_, v___x_3811_);
v___x_3813_ = lean_array_uset(v_bs_x27_3808_, v_i_3802_, v___y_3810_);
v_i_3802_ = v___x_3812_;
v_bs_3803_ = v___x_3813_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3820_, lean_object* v_sz_3821_, lean_object* v_i_3822_, lean_object* v_bs_3823_){
_start:
{
size_t v_sz_boxed_3824_; size_t v_i_boxed_3825_; lean_object* v_res_3826_; 
v_sz_boxed_3824_ = lean_unbox_usize(v_sz_3821_);
lean_dec(v_sz_3821_);
v_i_boxed_3825_ = lean_unbox_usize(v_i_3822_);
lean_dec(v_i_3822_);
v_res_3826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3820_, v_sz_boxed_3824_, v_i_boxed_3825_, v_bs_3823_);
lean_dec_ref(v_lctx_3820_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3827_, lean_object* v_pivot_3828_, lean_object* v_as_3829_, lean_object* v_i_3830_, lean_object* v_k_3831_){
_start:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_nat_dec_lt(v_k_3831_, v_hi_3827_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec(v_k_3831_);
v___x_3833_ = lean_array_fswap(v_as_3829_, v_i_3830_, v_hi_3827_);
v___x_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3834_, 0, v_i_3830_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
return v___x_3834_;
}
else
{
lean_object* v___x_3835_; lean_object* v_fst_3836_; lean_object* v_fst_3837_; uint8_t v___x_3838_; 
v___x_3835_ = lean_array_fget_borrowed(v_as_3829_, v_k_3831_);
v_fst_3836_ = lean_ctor_get(v___x_3835_, 0);
v_fst_3837_ = lean_ctor_get(v_pivot_3828_, 0);
v___x_3838_ = lean_nat_dec_lt(v_fst_3836_, v_fst_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_nat_add(v_k_3831_, v___x_3839_);
lean_dec(v_k_3831_);
v_k_3831_ = v___x_3840_;
goto _start;
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3842_ = lean_array_fswap(v_as_3829_, v_i_3830_, v_k_3831_);
v___x_3843_ = lean_unsigned_to_nat(1u);
v___x_3844_ = lean_nat_add(v_i_3830_, v___x_3843_);
lean_dec(v_i_3830_);
v___x_3845_ = lean_nat_add(v_k_3831_, v___x_3843_);
lean_dec(v_k_3831_);
v_as_3829_ = v___x_3842_;
v_i_3830_ = v___x_3844_;
v_k_3831_ = v___x_3845_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3847_, lean_object* v_pivot_3848_, lean_object* v_as_3849_, lean_object* v_i_3850_, lean_object* v_k_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3847_, v_pivot_3848_, v_as_3849_, v_i_3850_, v_k_3851_);
lean_dec_ref(v_pivot_3848_);
lean_dec(v_hi_3847_);
return v_res_3852_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3853_, lean_object* v_i_3854_){
_start:
{
lean_object* v_fst_3855_; lean_object* v_fst_3856_; uint8_t v___x_3857_; 
v_fst_3855_ = lean_ctor_get(v_h_3853_, 0);
v_fst_3856_ = lean_ctor_get(v_i_3854_, 0);
v___x_3857_ = lean_nat_dec_lt(v_fst_3855_, v_fst_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3858_, lean_object* v_i_3859_){
_start:
{
uint8_t v_res_3860_; lean_object* v_r_3861_; 
v_res_3860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3858_, v_i_3859_);
lean_dec_ref(v_i_3859_);
lean_dec_ref(v_h_3858_);
v_r_3861_ = lean_box(v_res_3860_);
return v_r_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3862_, lean_object* v_as_3863_, lean_object* v_lo_3864_, lean_object* v_hi_3865_){
_start:
{
lean_object* v___y_3867_; uint8_t v___x_3877_; 
v___x_3877_ = lean_nat_dec_lt(v_lo_3864_, v_hi_3865_);
if (v___x_3877_ == 0)
{
lean_dec(v_lo_3864_);
return v_as_3863_;
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v_mid_3880_; lean_object* v___y_3882_; lean_object* v___y_3888_; lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3878_ = lean_nat_add(v_lo_3864_, v_hi_3865_);
v___x_3879_ = lean_unsigned_to_nat(1u);
v_mid_3880_ = lean_nat_shiftr(v___x_3878_, v___x_3879_);
lean_dec(v___x_3878_);
v___x_3893_ = lean_array_fget_borrowed(v_as_3863_, v_mid_3880_);
v___x_3894_ = lean_array_fget_borrowed(v_as_3863_, v_lo_3864_);
v___x_3895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3893_, v___x_3894_);
if (v___x_3895_ == 0)
{
v___y_3888_ = v_as_3863_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_array_fswap(v_as_3863_, v_lo_3864_, v_mid_3880_);
v___y_3888_ = v___x_3896_;
goto v___jp_3887_;
}
v___jp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3883_ = lean_array_fget_borrowed(v___y_3882_, v_mid_3880_);
v___x_3884_ = lean_array_fget_borrowed(v___y_3882_, v_hi_3865_);
v___x_3885_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3883_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_dec(v_mid_3880_);
v___y_3867_ = v___y_3882_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_array_fswap(v___y_3882_, v_mid_3880_, v_hi_3865_);
lean_dec(v_mid_3880_);
v___y_3867_ = v___x_3886_;
goto v___jp_3866_;
}
}
v___jp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3889_ = lean_array_fget_borrowed(v___y_3888_, v_hi_3865_);
v___x_3890_ = lean_array_fget_borrowed(v___y_3888_, v_lo_3864_);
v___x_3891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3889_, v___x_3890_);
if (v___x_3891_ == 0)
{
v___y_3882_ = v___y_3888_;
goto v___jp_3881_;
}
else
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_array_fswap(v___y_3888_, v_lo_3864_, v_hi_3865_);
v___y_3882_ = v___x_3892_;
goto v___jp_3881_;
}
}
}
v___jp_3866_:
{
lean_object* v_pivot_3868_; lean_object* v___x_3869_; lean_object* v_fst_3870_; lean_object* v_snd_3871_; uint8_t v___x_3872_; 
v_pivot_3868_ = lean_array_fget(v___y_3867_, v_hi_3865_);
lean_inc_n(v_lo_3864_, 2);
v___x_3869_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3865_, v_pivot_3868_, v___y_3867_, v_lo_3864_, v_lo_3864_);
lean_dec(v_pivot_3868_);
v_fst_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_fst_3870_);
v_snd_3871_ = lean_ctor_get(v___x_3869_, 1);
lean_inc(v_snd_3871_);
lean_dec_ref(v___x_3869_);
v___x_3872_ = lean_nat_dec_le(v_hi_3865_, v_fst_3870_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3862_, v_snd_3871_, v_lo_3864_, v_fst_3870_);
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = lean_nat_add(v_fst_3870_, v___x_3874_);
lean_dec(v_fst_3870_);
v_as_3863_ = v___x_3873_;
v_lo_3864_ = v___x_3875_;
goto _start;
}
else
{
lean_dec(v_fst_3870_);
lean_dec(v_lo_3864_);
return v_snd_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3897_, lean_object* v_as_3898_, lean_object* v_lo_3899_, lean_object* v_hi_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3897_, v_as_3898_, v_lo_3899_, v_hi_3900_);
lean_dec(v_hi_3900_);
lean_dec(v_n_3897_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3902_, lean_object* v_hyps_3903_){
_start:
{
lean_object* v___y_3905_; size_t v_sz_3909_; size_t v___x_3910_; lean_object* v_hyps_3911_; lean_object* v___x_3912_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v_sz_3909_ = lean_array_size(v_hyps_3903_);
v___x_3910_ = ((size_t)0ULL);
v_hyps_3911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3902_, v_sz_3909_, v___x_3910_, v_hyps_3903_);
v___x_3912_ = lean_array_get_size(v_hyps_3911_);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = lean_nat_dec_eq(v___x_3912_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___y_3922_; uint8_t v___x_3924_; 
v___x_3919_ = lean_unsigned_to_nat(1u);
v___x_3920_ = lean_nat_sub(v___x_3912_, v___x_3919_);
v___x_3924_ = lean_nat_dec_le(v___x_3917_, v___x_3920_);
if (v___x_3924_ == 0)
{
lean_inc(v___x_3920_);
v___y_3922_ = v___x_3920_;
goto v___jp_3921_;
}
else
{
v___y_3922_ = v___x_3917_;
goto v___jp_3921_;
}
v___jp_3921_:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_nat_dec_le(v___y_3922_, v___x_3920_);
if (v___x_3923_ == 0)
{
lean_dec(v___x_3920_);
lean_inc(v___y_3922_);
v___y_3914_ = v___y_3922_;
v___y_3915_ = v___y_3922_;
goto v___jp_3913_;
}
else
{
v___y_3914_ = v___y_3922_;
v___y_3915_ = v___x_3920_;
goto v___jp_3913_;
}
}
}
else
{
v___y_3905_ = v_hyps_3911_;
goto v___jp_3904_;
}
v___jp_3904_:
{
size_t v_sz_3906_; size_t v___x_3907_; lean_object* v___x_3908_; 
v_sz_3906_ = lean_array_size(v___y_3905_);
v___x_3907_ = ((size_t)0ULL);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3906_, v___x_3907_, v___y_3905_);
return v___x_3908_;
}
v___jp_3913_:
{
lean_object* v___x_3916_; 
v___x_3916_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3912_, v_hyps_3911_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
v___y_3905_ = v___x_3916_;
goto v___jp_3904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3925_, lean_object* v_hyps_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3925_, v_hyps_3926_);
lean_dec_ref(v_lctx_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3928_, lean_object* v_as_3929_, lean_object* v_lo_3930_, lean_object* v_hi_3931_, lean_object* v_w_3932_, lean_object* v_hlo_3933_, lean_object* v_hhi_3934_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3928_, v_as_3929_, v_lo_3930_, v_hi_3931_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3936_, lean_object* v_as_3937_, lean_object* v_lo_3938_, lean_object* v_hi_3939_, lean_object* v_w_3940_, lean_object* v_hlo_3941_, lean_object* v_hhi_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3936_, v_as_3937_, v_lo_3938_, v_hi_3939_, v_w_3940_, v_hlo_3941_, v_hhi_3942_);
lean_dec(v_hi_3939_);
lean_dec(v_n_3936_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3944_, lean_object* v_lo_3945_, lean_object* v_hi_3946_, lean_object* v_hhi_3947_, lean_object* v_pivot_3948_, lean_object* v_as_3949_, lean_object* v_i_3950_, lean_object* v_k_3951_, lean_object* v_ilo_3952_, lean_object* v_ik_3953_, lean_object* v_w_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3946_, v_pivot_3948_, v_as_3949_, v_i_3950_, v_k_3951_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_3956_, lean_object* v_lo_3957_, lean_object* v_hi_3958_, lean_object* v_hhi_3959_, lean_object* v_pivot_3960_, lean_object* v_as_3961_, lean_object* v_i_3962_, lean_object* v_k_3963_, lean_object* v_ilo_3964_, lean_object* v_ik_3965_, lean_object* v_w_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_3956_, v_lo_3957_, v_hi_3958_, v_hhi_3959_, v_pivot_3960_, v_as_3961_, v_i_3962_, v_k_3963_, v_ilo_3964_, v_ik_3965_, v_w_3966_);
lean_dec_ref(v_pivot_3960_);
lean_dec(v_hi_3958_);
lean_dec(v_lo_3957_);
lean_dec(v_n_3956_);
return v_res_3967_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3968_, lean_object* v_x_3969_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
uint8_t v___x_3970_; 
v___x_3970_ = 0;
return v___x_3970_;
}
else
{
lean_object* v_key_3971_; lean_object* v_tail_3972_; uint8_t v___x_3973_; 
v_key_3971_ = lean_ctor_get(v_x_3969_, 0);
v_tail_3972_ = lean_ctor_get(v_x_3969_, 2);
v___x_3973_ = lean_name_eq(v_key_3971_, v_a_3968_);
if (v___x_3973_ == 0)
{
v_x_3969_ = v_tail_3972_;
goto _start;
}
else
{
return v___x_3973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3975_, lean_object* v_x_3976_){
_start:
{
uint8_t v_res_3977_; lean_object* v_r_3978_; 
v_res_3977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3975_, v_x_3976_);
lean_dec(v_x_3976_);
lean_dec(v_a_3975_);
v_r_3978_ = lean_box(v_res_3977_);
return v_r_3978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3979_, lean_object* v_x_3980_){
_start:
{
if (lean_obj_tag(v_x_3980_) == 0)
{
return v_x_3980_;
}
else
{
lean_object* v_key_3981_; lean_object* v_value_3982_; lean_object* v_tail_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3992_; 
v_key_3981_ = lean_ctor_get(v_x_3980_, 0);
v_value_3982_ = lean_ctor_get(v_x_3980_, 1);
v_tail_3983_ = lean_ctor_get(v_x_3980_, 2);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_x_3980_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3985_ = v_x_3980_;
v_isShared_3986_ = v_isSharedCheck_3992_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_tail_3983_);
lean_inc(v_value_3982_);
lean_inc(v_key_3981_);
lean_dec(v_x_3980_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3992_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
uint8_t v___x_3987_; 
v___x_3987_ = lean_name_eq(v_key_3981_, v_a_3979_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3988_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3979_, v_tail_3983_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 2, v___x_3988_);
v___x_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_key_3981_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_value_3982_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
else
{
lean_del_object(v___x_3985_);
lean_dec(v_value_3982_);
lean_dec(v_key_3981_);
return v_tail_3983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3993_, lean_object* v_x_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3993_, v_x_3994_);
lean_dec(v_a_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_size_3998_; lean_object* v_buckets_3999_; lean_object* v___x_4000_; uint64_t v___y_4002_; 
v_size_3998_ = lean_ctor_get(v_m_3996_, 0);
v_buckets_3999_ = lean_ctor_get(v_m_3996_, 1);
v___x_4000_ = lean_array_get_size(v_buckets_3999_);
if (lean_obj_tag(v_a_3997_) == 0)
{
uint64_t v___x_4031_; 
v___x_4031_ = 1723ULL;
v___y_4002_ = v___x_4031_;
goto v___jp_4001_;
}
else
{
uint64_t v_hash_4032_; 
v_hash_4032_ = lean_ctor_get_uint64(v_a_3997_, sizeof(void*)*2);
v___y_4002_ = v_hash_4032_;
goto v___jp_4001_;
}
v___jp_4001_:
{
uint64_t v___x_4003_; uint64_t v___x_4004_; uint64_t v_fold_4005_; uint64_t v___x_4006_; uint64_t v___x_4007_; uint64_t v___x_4008_; size_t v___x_4009_; size_t v___x_4010_; size_t v___x_4011_; size_t v___x_4012_; size_t v___x_4013_; lean_object* v_bkt_4014_; uint8_t v___x_4015_; 
v___x_4003_ = 32ULL;
v___x_4004_ = lean_uint64_shift_right(v___y_4002_, v___x_4003_);
v_fold_4005_ = lean_uint64_xor(v___y_4002_, v___x_4004_);
v___x_4006_ = 16ULL;
v___x_4007_ = lean_uint64_shift_right(v_fold_4005_, v___x_4006_);
v___x_4008_ = lean_uint64_xor(v_fold_4005_, v___x_4007_);
v___x_4009_ = lean_uint64_to_usize(v___x_4008_);
v___x_4010_ = lean_usize_of_nat(v___x_4000_);
v___x_4011_ = ((size_t)1ULL);
v___x_4012_ = lean_usize_sub(v___x_4010_, v___x_4011_);
v___x_4013_ = lean_usize_land(v___x_4009_, v___x_4012_);
v_bkt_4014_ = lean_array_uget_borrowed(v_buckets_3999_, v___x_4013_);
v___x_4015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3997_, v_bkt_4014_);
if (v___x_4015_ == 0)
{
return v_m_3996_;
}
else
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4028_; 
lean_inc(v_bkt_4014_);
lean_inc_ref(v_buckets_3999_);
lean_inc(v_size_3998_);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_m_3996_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; lean_object* v_unused_4030_; 
v_unused_4029_ = lean_ctor_get(v_m_3996_, 1);
lean_dec(v_unused_4029_);
v_unused_4030_ = lean_ctor_get(v_m_3996_, 0);
lean_dec(v_unused_4030_);
v___x_4017_ = v_m_3996_;
v_isShared_4018_ = v_isSharedCheck_4028_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v_m_3996_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4028_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v_buckets_x27_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4019_ = lean_box(0);
v_buckets_x27_4020_ = lean_array_uset(v_buckets_3999_, v___x_4013_, v___x_4019_);
v___x_4021_ = lean_unsigned_to_nat(1u);
v___x_4022_ = lean_nat_sub(v_size_3998_, v___x_4021_);
lean_dec(v_size_3998_);
v___x_4023_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3997_, v_bkt_4014_);
v___x_4024_ = lean_array_uset(v_buckets_x27_4020_, v___x_4013_, v___x_4023_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4024_);
lean_ctor_set(v___x_4017_, 0, v___x_4022_);
v___x_4026_ = v___x_4017_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4033_, v_a_4034_);
lean_dec(v_a_4034_);
return v_res_4035_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_buckets_4038_; lean_object* v___x_4039_; uint64_t v___y_4041_; 
v_buckets_4038_ = lean_ctor_get(v_m_4036_, 1);
v___x_4039_ = lean_array_get_size(v_buckets_4038_);
if (lean_obj_tag(v_a_4037_) == 0)
{
uint64_t v___x_4055_; 
v___x_4055_ = 1723ULL;
v___y_4041_ = v___x_4055_;
goto v___jp_4040_;
}
else
{
uint64_t v_hash_4056_; 
v_hash_4056_ = lean_ctor_get_uint64(v_a_4037_, sizeof(void*)*2);
v___y_4041_ = v_hash_4056_;
goto v___jp_4040_;
}
v___jp_4040_:
{
uint64_t v___x_4042_; uint64_t v___x_4043_; uint64_t v_fold_4044_; uint64_t v___x_4045_; uint64_t v___x_4046_; uint64_t v___x_4047_; size_t v___x_4048_; size_t v___x_4049_; size_t v___x_4050_; size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4042_ = 32ULL;
v___x_4043_ = lean_uint64_shift_right(v___y_4041_, v___x_4042_);
v_fold_4044_ = lean_uint64_xor(v___y_4041_, v___x_4043_);
v___x_4045_ = 16ULL;
v___x_4046_ = lean_uint64_shift_right(v_fold_4044_, v___x_4045_);
v___x_4047_ = lean_uint64_xor(v_fold_4044_, v___x_4046_);
v___x_4048_ = lean_uint64_to_usize(v___x_4047_);
v___x_4049_ = lean_usize_of_nat(v___x_4039_);
v___x_4050_ = ((size_t)1ULL);
v___x_4051_ = lean_usize_sub(v___x_4049_, v___x_4050_);
v___x_4052_ = lean_usize_land(v___x_4048_, v___x_4051_);
v___x_4053_ = lean_array_uget_borrowed(v_buckets_4038_, v___x_4052_);
v___x_4054_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4037_, v___x_4053_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4057_, lean_object* v_a_4058_){
_start:
{
uint8_t v_res_4059_; lean_object* v_r_4060_; 
v_res_4059_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4057_, v_a_4058_);
lean_dec(v_a_4058_);
lean_dec_ref(v_m_4057_);
v_r_4060_ = lean_box(v_res_4059_);
return v_r_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4061_, lean_object* v_as_4062_, size_t v_i_4063_, size_t v_stop_4064_, lean_object* v_b_4065_){
_start:
{
uint8_t v___x_4066_; 
v___x_4066_ = lean_usize_dec_eq(v_i_4063_, v_stop_4064_);
if (v___x_4066_ == 0)
{
size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((size_t)1ULL);
v___x_4068_ = lean_usize_sub(v_i_4063_, v___x_4067_);
v___x_4069_ = lean_array_uget(v_as_4062_, v___x_4068_);
if (lean_obj_tag(v___x_4069_) == 0)
{
v_i_4063_ = v___x_4068_;
goto _start;
}
else
{
lean_object* v_val_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4105_; 
v_val_4071_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4073_ = v___x_4069_;
v_isShared_4074_ = v_isSharedCheck_4105_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_val_4071_);
lean_dec(v___x_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4105_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v_fst_4075_; lean_object* v_snd_4076_; lean_object* v___y_4078_; lean_object* v___y_4094_; lean_object* v_size_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; 
v_fst_4075_ = lean_ctor_get(v_b_4065_, 0);
v_snd_4076_ = lean_ctor_get(v_b_4065_, 1);
v_size_4100_ = lean_ctor_get(v_fst_4075_, 0);
v___x_4101_ = lean_unsigned_to_nat(0u);
v___x_4102_ = lean_nat_dec_eq(v_size_4100_, v___x_4101_);
if (v___x_4102_ == 0)
{
lean_object* v_index_4103_; 
v_index_4103_ = lean_ctor_get(v_val_4071_, 0);
lean_inc(v_index_4103_);
v___y_4094_ = v_index_4103_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4104_; 
lean_inc(v_snd_4076_);
lean_del_object(v___x_4073_);
lean_dec(v_val_4071_);
lean_dec_ref(v_b_4065_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_snd_4076_);
return v___x_4104_;
}
v___jp_4077_:
{
uint8_t v___x_4079_; 
v___x_4079_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4075_, v___y_4078_);
if (v___x_4079_ == 0)
{
lean_dec(v___y_4078_);
lean_dec(v_val_4071_);
v_i_4063_ = v___x_4068_;
goto _start;
}
else
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4090_; 
lean_inc(v_snd_4076_);
lean_inc(v_fst_4075_);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_b_4065_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; lean_object* v_unused_4092_; 
v_unused_4091_ = lean_ctor_get(v_b_4065_, 1);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_b_4065_, 0);
lean_dec(v_unused_4092_);
v___x_4082_ = v_b_4065_;
v_isShared_4083_ = v_isSharedCheck_4090_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v_b_4065_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4090_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4075_, v___y_4078_);
lean_dec(v___y_4078_);
v___x_4085_ = lean_array_push(v_snd_4076_, v_val_4071_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 1, v___x_4085_);
lean_ctor_set(v___x_4082_, 0, v___x_4084_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
v_i_4063_ = v___x_4068_;
v_b_4065_ = v___x_4087_;
goto _start;
}
}
}
}
v___jp_4093_:
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_nat_dec_lt(v___y_4094_, v_start_4061_);
lean_dec(v___y_4094_);
if (v___x_4095_ == 0)
{
lean_object* v_userName_4096_; 
lean_del_object(v___x_4073_);
v_userName_4096_ = lean_ctor_get(v_val_4071_, 2);
lean_inc(v_userName_4096_);
v___y_4078_ = v_userName_4096_;
goto v___jp_4077_;
}
else
{
lean_object* v___x_4098_; 
lean_inc(v_snd_4076_);
lean_dec(v_val_4071_);
lean_dec_ref(v_b_4065_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set_tag(v___x_4073_, 0);
lean_ctor_set(v___x_4073_, 0, v_snd_4076_);
v___x_4098_ = v___x_4073_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_snd_4076_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
else
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_b_4065_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4107_, lean_object* v_as_4108_, lean_object* v_i_4109_, lean_object* v_stop_4110_, lean_object* v_b_4111_){
_start:
{
size_t v_i_boxed_4112_; size_t v_stop_boxed_4113_; lean_object* v_res_4114_; 
v_i_boxed_4112_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_stop_boxed_4113_ = lean_unbox_usize(v_stop_4110_);
lean_dec(v_stop_4110_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4107_, v_as_4108_, v_i_boxed_4112_, v_stop_boxed_4113_, v_b_4111_);
lean_dec_ref(v_as_4108_);
lean_dec(v_start_4107_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4115_, lean_object* v_x_4116_, lean_object* v_x_4117_){
_start:
{
if (lean_obj_tag(v_x_4116_) == 0)
{
lean_object* v_cs_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4131_; 
v_cs_4118_ = lean_ctor_get(v_x_4116_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v_x_4116_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4120_ = v_x_4116_;
v_isShared_4121_ = v_isSharedCheck_4131_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_cs_4118_);
lean_dec(v_x_4116_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4131_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4122_ = lean_array_get_size(v_cs_4118_);
v___x_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = lean_nat_dec_lt(v___x_4123_, v___x_4122_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4126_; 
lean_dec_ref(v_cs_4118_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set_tag(v___x_4120_, 1);
lean_ctor_set(v___x_4120_, 0, v_x_4117_);
v___x_4126_ = v___x_4120_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_x_4117_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
else
{
size_t v___x_4128_; size_t v___x_4129_; lean_object* v___x_4130_; 
lean_del_object(v___x_4120_);
v___x_4128_ = lean_usize_of_nat(v___x_4122_);
v___x_4129_ = ((size_t)0ULL);
v___x_4130_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4115_, v_cs_4118_, v___x_4128_, v___x_4129_, v_x_4117_);
lean_dec_ref(v_cs_4118_);
return v___x_4130_;
}
}
}
else
{
lean_object* v_vs_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4145_; 
v_vs_4132_ = lean_ctor_get(v_x_4116_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_x_4116_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4134_ = v_x_4116_;
v_isShared_4135_ = v_isSharedCheck_4145_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_vs_4132_);
lean_dec(v_x_4116_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4145_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4136_ = lean_array_get_size(v_vs_4132_);
v___x_4137_ = lean_unsigned_to_nat(0u);
v___x_4138_ = lean_nat_dec_lt(v___x_4137_, v___x_4136_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4140_; 
lean_dec_ref(v_vs_4132_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v_x_4117_);
v___x_4140_ = v___x_4134_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_x_4117_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
else
{
size_t v___x_4142_; size_t v___x_4143_; lean_object* v___x_4144_; 
lean_del_object(v___x_4134_);
v___x_4142_ = lean_usize_of_nat(v___x_4136_);
v___x_4143_ = ((size_t)0ULL);
v___x_4144_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4115_, v_vs_4132_, v___x_4142_, v___x_4143_, v_x_4117_);
lean_dec_ref(v_vs_4132_);
return v___x_4144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4146_, lean_object* v_as_4147_, size_t v_i_4148_, size_t v_stop_4149_, lean_object* v_b_4150_){
_start:
{
uint8_t v___x_4151_; 
v___x_4151_ = lean_usize_dec_eq(v_i_4148_, v_stop_4149_);
if (v___x_4151_ == 0)
{
size_t v___x_4152_; size_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4152_ = ((size_t)1ULL);
v___x_4153_ = lean_usize_sub(v_i_4148_, v___x_4152_);
v___x_4154_ = lean_array_uget_borrowed(v_as_4147_, v___x_4153_);
lean_inc(v___x_4154_);
v___x_4155_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4146_, v___x_4154_, v_b_4150_);
if (lean_obj_tag(v___x_4155_) == 0)
{
return v___x_4155_;
}
else
{
lean_object* v_a_4156_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v_i_4148_ = v___x_4153_;
v_b_4150_ = v_a_4156_;
goto _start;
}
}
else
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4158_, 0, v_b_4150_);
return v___x_4158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4159_, lean_object* v_as_4160_, lean_object* v_i_4161_, lean_object* v_stop_4162_, lean_object* v_b_4163_){
_start:
{
size_t v_i_boxed_4164_; size_t v_stop_boxed_4165_; lean_object* v_res_4166_; 
v_i_boxed_4164_ = lean_unbox_usize(v_i_4161_);
lean_dec(v_i_4161_);
v_stop_boxed_4165_ = lean_unbox_usize(v_stop_4162_);
lean_dec(v_stop_4162_);
v_res_4166_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4159_, v_as_4160_, v_i_boxed_4164_, v_stop_boxed_4165_, v_b_4163_);
lean_dec_ref(v_as_4160_);
lean_dec(v_start_4159_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4167_, lean_object* v_x_4168_, lean_object* v_x_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4167_, v_x_4168_, v_x_4169_);
lean_dec(v_start_4167_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4171_, lean_object* v_t_4172_, lean_object* v_init_4173_){
_start:
{
lean_object* v_root_4174_; lean_object* v_tail_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
v_root_4174_ = lean_ctor_get(v_t_4172_, 0);
lean_inc_ref(v_root_4174_);
v_tail_4175_ = lean_ctor_get(v_t_4172_, 1);
lean_inc_ref(v_tail_4175_);
lean_dec_ref(v_t_4172_);
v___x_4176_ = lean_array_get_size(v_tail_4175_);
v___x_4177_ = lean_unsigned_to_nat(0u);
v___x_4178_ = lean_nat_dec_lt(v___x_4177_, v___x_4176_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; 
lean_dec_ref(v_tail_4175_);
v___x_4179_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4171_, v_root_4174_, v_init_4173_);
return v___x_4179_;
}
else
{
size_t v___x_4180_; size_t v___x_4181_; lean_object* v___x_4182_; 
v___x_4180_ = lean_usize_of_nat(v___x_4176_);
v___x_4181_ = ((size_t)0ULL);
v___x_4182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4171_, v_tail_4175_, v___x_4180_, v___x_4181_, v_init_4173_);
lean_dec_ref(v_tail_4175_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_dec_ref(v_root_4174_);
return v___x_4182_;
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4184_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v___x_4184_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4171_, v_root_4174_, v_a_4183_);
return v___x_4184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4185_, lean_object* v_t_4186_, lean_object* v_init_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4185_, v_t_4186_, v_init_4187_);
lean_dec(v_start_4185_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4189_, lean_object* v_lctx_4190_, lean_object* v_init_4191_){
_start:
{
lean_object* v_decls_4192_; lean_object* v___x_4193_; 
v_decls_4192_ = lean_ctor_get(v_lctx_4190_, 1);
lean_inc_ref(v_decls_4192_);
lean_dec_ref(v_lctx_4190_);
v___x_4193_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4189_, v_decls_4192_, v_init_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4194_, lean_object* v_lctx_4195_, lean_object* v_init_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4194_, v_lctx_4195_, v_init_4196_);
lean_dec(v_start_4194_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4200_, lean_object* v_userNames_4201_, lean_object* v_start_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4203_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_userNames_4201_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4202_, v_lctx_4200_, v___x_4204_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = l_Array_reverse___redArg(v_a_4206_);
return v___x_4207_;
}
else
{
lean_object* v_a_4208_; lean_object* v_snd_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v_a_4208_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4205_, 1);
v_snd_4209_ = lean_ctor_get(v_a_4208_, 1);
lean_inc(v_snd_4209_);
lean_dec(v_a_4208_);
v___x_4210_ = l_Array_reverse___redArg(v_snd_4209_);
v___x_4211_ = l_Array_reverse___redArg(v___x_4210_);
return v___x_4211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4212_, lean_object* v_userNames_4213_, lean_object* v_start_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4212_, v_userNames_4213_, v_start_4214_);
lean_dec(v_start_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4216_, lean_object* v_lctx_4217_, lean_object* v_userNames_4218_, lean_object* v_start_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4217_, v_userNames_4218_, v_start_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4221_, lean_object* v_lctx_4222_, lean_object* v_userNames_4223_, lean_object* v_start_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4221_, v_lctx_4222_, v_userNames_4223_, v_start_4224_);
lean_dec(v_start_4224_);
return v_res_4225_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4226_, lean_object* v_m_4227_, lean_object* v_a_4228_){
_start:
{
uint8_t v___x_4229_; 
v___x_4229_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4227_, v_a_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4230_, lean_object* v_m_4231_, lean_object* v_a_4232_){
_start:
{
uint8_t v_res_4233_; lean_object* v_r_4234_; 
v_res_4233_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4230_, v_m_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_m_4231_);
v_r_4234_ = lean_box(v_res_4233_);
return v_r_4234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4235_, lean_object* v_m_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4236_, v_a_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4239_, lean_object* v_m_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4239_, v_m_4240_, v_a_4241_);
lean_dec(v_a_4241_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4243_, lean_object* v_start_4244_, lean_object* v_lctx_4245_, lean_object* v_init_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4244_, v_lctx_4245_, v_init_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_start_4249_, lean_object* v_lctx_4250_, lean_object* v_init_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4248_, v_start_4249_, v_lctx_4250_, v_init_4251_);
lean_dec(v_start_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4253_, lean_object* v_a_4254_, lean_object* v_x_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4254_, v_x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4257_, lean_object* v_a_4258_, lean_object* v_x_4259_){
_start:
{
uint8_t v_res_4260_; lean_object* v_r_4261_; 
v_res_4260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4257_, v_a_4258_, v_x_4259_);
lean_dec(v_x_4259_);
lean_dec(v_a_4258_);
v_r_4261_ = lean_box(v_res_4260_);
return v_r_4261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4262_, lean_object* v_a_4263_, lean_object* v_x_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4263_, v_x_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4266_, lean_object* v_a_4267_, lean_object* v_x_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4266_, v_a_4267_, v_x_4268_);
lean_dec(v_a_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4270_, lean_object* v_start_4271_, lean_object* v_t_4272_, lean_object* v_init_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4271_, v_t_4272_, v_init_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4275_, lean_object* v_start_4276_, lean_object* v_t_4277_, lean_object* v_init_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4275_, v_start_4276_, v_t_4277_, v_init_4278_);
lean_dec(v_start_4276_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4280_, lean_object* v_start_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4281_, v_x_4282_, v_x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4285_, lean_object* v_start_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4285_, v_start_4286_, v_x_4287_, v_x_4288_);
lean_dec(v_start_4286_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4290_, lean_object* v_start_4291_, lean_object* v_as_4292_, size_t v_i_4293_, size_t v_stop_4294_, lean_object* v_b_4295_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4291_, v_as_4292_, v_i_4293_, v_stop_4294_, v_b_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4297_, lean_object* v_start_4298_, lean_object* v_as_4299_, lean_object* v_i_4300_, lean_object* v_stop_4301_, lean_object* v_b_4302_){
_start:
{
size_t v_i_boxed_4303_; size_t v_stop_boxed_4304_; lean_object* v_res_4305_; 
v_i_boxed_4303_ = lean_unbox_usize(v_i_4300_);
lean_dec(v_i_4300_);
v_stop_boxed_4304_ = lean_unbox_usize(v_stop_4301_);
lean_dec(v_stop_4301_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4297_, v_start_4298_, v_as_4299_, v_i_boxed_4303_, v_stop_boxed_4304_, v_b_4302_);
lean_dec_ref(v_as_4299_);
lean_dec(v_start_4298_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4306_, lean_object* v_start_4307_, lean_object* v_as_4308_, size_t v_i_4309_, size_t v_stop_4310_, lean_object* v_b_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4307_, v_as_4308_, v_i_4309_, v_stop_4310_, v_b_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4313_, lean_object* v_start_4314_, lean_object* v_as_4315_, lean_object* v_i_4316_, lean_object* v_stop_4317_, lean_object* v_b_4318_){
_start:
{
size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; lean_object* v_res_4321_; 
v_i_boxed_4319_ = lean_unbox_usize(v_i_4316_);
lean_dec(v_i_4316_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4317_);
lean_dec(v_stop_4317_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4313_, v_start_4314_, v_as_4315_, v_i_boxed_4319_, v_stop_boxed_4320_, v_b_4318_);
lean_dec_ref(v_as_4315_);
lean_dec(v_start_4314_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4322_, lean_object* v_inst_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = lean_apply_2(v_inst_4322_, lean_box(0), v_inst_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4325_, lean_object* v_n_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_apply_2(v_inst_4327_, lean_box(0), v_inst_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4330_, lean_object* v_d_x3f_4331_, lean_object* v_b_4332_){
_start:
{
if (lean_obj_tag(v_d_x3f_4331_) == 0)
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4333_, 0, v_b_4332_);
v___x_4334_ = lean_apply_2(v_toPure_4330_, lean_box(0), v___x_4333_);
return v___x_4334_;
}
else
{
lean_object* v_val_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4350_; 
v_val_4335_ = lean_ctor_get(v_d_x3f_4331_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_d_x3f_4331_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4337_ = v_d_x3f_4331_;
v_isShared_4338_ = v_isSharedCheck_4350_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_val_4335_);
lean_dec(v_d_x3f_4331_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4350_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
uint8_t v___x_4339_; 
v___x_4339_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4335_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4340_ = l_Lean_LocalDecl_toExpr(v_val_4335_);
v___x_4341_ = lean_array_push(v_b_4332_, v___x_4340_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v___x_4341_);
v___x_4343_ = v___x_4337_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_apply_2(v_toPure_4330_, lean_box(0), v___x_4343_);
return v___x_4344_;
}
}
else
{
lean_object* v___x_4347_; 
lean_dec(v_val_4335_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v_b_4332_);
v___x_4347_ = v___x_4337_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_b_4332_);
v___x_4347_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; 
v___x_4348_ = lean_apply_2(v_toPure_4330_, lean_box(0), v___x_4347_);
return v___x_4348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4351_, lean_object* v_____s_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_apply_2(v_toPure_4351_, lean_box(0), v_____s_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4354_, lean_object* v_hs_4355_, lean_object* v___f_4356_, lean_object* v_toBind_4357_, lean_object* v___f_4358_, lean_object* v_____do__lift_4359_){
_start:
{
lean_object* v_decls_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_decls_4360_ = lean_ctor_get(v_____do__lift_4359_, 1);
v___x_4361_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4354_, v_decls_4360_, v_hs_4355_, v___f_4356_);
v___x_4362_ = lean_apply_4(v_toBind_4357_, lean_box(0), lean_box(0), v___x_4361_, v___f_4358_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4363_, lean_object* v_hs_4364_, lean_object* v___f_4365_, lean_object* v_toBind_4366_, lean_object* v___f_4367_, lean_object* v_____do__lift_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4363_, v_hs_4364_, v___f_4365_, v_toBind_4366_, v___f_4367_, v_____do__lift_4368_);
lean_dec_ref(v_____do__lift_4368_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4372_, lean_object* v_inst_4373_){
_start:
{
lean_object* v_toApplicative_4374_; lean_object* v_toBind_4375_; lean_object* v_toPure_4376_; lean_object* v_hs_4377_; lean_object* v___f_4378_; lean_object* v___f_4379_; lean_object* v___f_4380_; lean_object* v___x_4381_; 
v_toApplicative_4374_ = lean_ctor_get(v_inst_4372_, 0);
v_toBind_4375_ = lean_ctor_get(v_inst_4372_, 1);
lean_inc_n(v_toBind_4375_, 2);
v_toPure_4376_ = lean_ctor_get(v_toApplicative_4374_, 1);
v_hs_4377_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4376_, 2);
v___f_4378_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4378_, 0, v_toPure_4376_);
v___f_4379_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4379_, 0, v_toPure_4376_);
v___f_4380_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4380_, 0, v_inst_4372_);
lean_closure_set(v___f_4380_, 1, v_hs_4377_);
lean_closure_set(v___f_4380_, 2, v___f_4378_);
lean_closure_set(v___f_4380_, 3, v_toBind_4375_);
lean_closure_set(v___f_4380_, 4, v___f_4379_);
v___x_4381_ = lean_apply_4(v_toBind_4375_, lean_box(0), lean_box(0), v_inst_4373_, v___f_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4382_, lean_object* v_inst_4383_, lean_object* v_inst_4384_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_getLocalHyps___redArg(v_inst_4383_, v_inst_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4386_, lean_object* v_e_4387_, lean_object* v_d_4388_){
_start:
{
lean_object* v___y_4390_; lean_object* v_fvarId_4422_; 
v_fvarId_4422_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_fvarId_4422_);
v___y_4390_ = v_fvarId_4422_;
goto v___jp_4389_;
v___jp_4389_:
{
uint8_t v___x_4391_; 
v___x_4391_ = l_Lean_instBEqFVarId_beq(v___y_4390_, v_fvarId_4386_);
lean_dec(v___y_4390_);
if (v___x_4391_ == 0)
{
if (lean_obj_tag(v_d_4388_) == 0)
{
lean_object* v_index_4392_; lean_object* v_fvarId_4393_; lean_object* v_userName_4394_; lean_object* v_type_4395_; uint8_t v_bi_4396_; uint8_t v_kind_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4405_; 
v_index_4392_ = lean_ctor_get(v_d_4388_, 0);
v_fvarId_4393_ = lean_ctor_get(v_d_4388_, 1);
v_userName_4394_ = lean_ctor_get(v_d_4388_, 2);
v_type_4395_ = lean_ctor_get(v_d_4388_, 3);
v_bi_4396_ = lean_ctor_get_uint8(v_d_4388_, sizeof(void*)*4);
v_kind_4397_ = lean_ctor_get_uint8(v_d_4388_, sizeof(void*)*4 + 1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_d_4388_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4399_ = v_d_4388_;
v_isShared_4400_ = v_isSharedCheck_4405_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_type_4395_);
lean_inc(v_userName_4394_);
lean_inc(v_fvarId_4393_);
lean_inc(v_index_4392_);
lean_dec(v_d_4388_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4405_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4401_ = l_Lean_Expr_replaceFVarId(v_type_4395_, v_fvarId_4386_, v_e_4387_);
lean_dec_ref(v_type_4395_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 3, v___x_4401_);
v___x_4403_ = v___x_4399_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_index_4392_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_fvarId_4393_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_userName_4394_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v___x_4401_);
lean_ctor_set_uint8(v_reuseFailAlloc_4404_, sizeof(void*)*4, v_bi_4396_);
lean_ctor_set_uint8(v_reuseFailAlloc_4404_, sizeof(void*)*4 + 1, v_kind_4397_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
else
{
lean_object* v_index_4406_; lean_object* v_fvarId_4407_; lean_object* v_userName_4408_; lean_object* v_type_4409_; lean_object* v_value_4410_; uint8_t v_nondep_4411_; uint8_t v_kind_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4421_; 
v_index_4406_ = lean_ctor_get(v_d_4388_, 0);
v_fvarId_4407_ = lean_ctor_get(v_d_4388_, 1);
v_userName_4408_ = lean_ctor_get(v_d_4388_, 2);
v_type_4409_ = lean_ctor_get(v_d_4388_, 3);
v_value_4410_ = lean_ctor_get(v_d_4388_, 4);
v_nondep_4411_ = lean_ctor_get_uint8(v_d_4388_, sizeof(void*)*5);
v_kind_4412_ = lean_ctor_get_uint8(v_d_4388_, sizeof(void*)*5 + 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_d_4388_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4414_ = v_d_4388_;
v_isShared_4415_ = v_isSharedCheck_4421_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_value_4410_);
lean_inc(v_type_4409_);
lean_inc(v_userName_4408_);
lean_inc(v_fvarId_4407_);
lean_inc(v_index_4406_);
lean_dec(v_d_4388_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4421_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
lean_inc(v_fvarId_4386_);
v___x_4416_ = l_Lean_Expr_replaceFVarId(v_type_4409_, v_fvarId_4386_, v_e_4387_);
lean_dec_ref(v_type_4409_);
v___x_4417_ = l_Lean_Expr_replaceFVarId(v_value_4410_, v_fvarId_4386_, v_e_4387_);
lean_dec_ref(v_value_4410_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 4, v___x_4417_);
lean_ctor_set(v___x_4414_, 3, v___x_4416_);
v___x_4419_ = v___x_4414_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_index_4406_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_fvarId_4407_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v_userName_4408_);
lean_ctor_set(v_reuseFailAlloc_4420_, 3, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4420_, 4, v___x_4417_);
lean_ctor_set_uint8(v_reuseFailAlloc_4420_, sizeof(void*)*5, v_nondep_4411_);
lean_ctor_set_uint8(v_reuseFailAlloc_4420_, sizeof(void*)*5 + 1, v_kind_4412_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
else
{
lean_dec(v_fvarId_4386_);
return v_d_4388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4423_, lean_object* v_e_4424_, lean_object* v_d_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4423_, v_e_4424_, v_d_4425_);
lean_dec_ref(v_e_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4427_, lean_object* v_e_4428_, lean_object* v_x_4429_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4427_, v_e_4428_, v_x_4429_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4431_, lean_object* v_e_4432_, lean_object* v_x_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4431_, v_e_4432_, v_x_4433_);
lean_dec_ref(v_e_4432_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4435_, lean_object* v_e_4436_, size_t v_sz_4437_, size_t v_i_4438_, lean_object* v_bs_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_lt(v_i_4438_, v_sz_4437_);
if (v___x_4440_ == 0)
{
lean_dec(v_fvarId_4435_);
return v_bs_4439_;
}
else
{
lean_object* v_v_4441_; lean_object* v___x_4442_; lean_object* v_bs_x27_4443_; lean_object* v___y_4445_; 
v_v_4441_ = lean_array_uget(v_bs_4439_, v_i_4438_);
v___x_4442_ = lean_unsigned_to_nat(0u);
v_bs_x27_4443_ = lean_array_uset(v_bs_4439_, v_i_4438_, v___x_4442_);
if (lean_obj_tag(v_v_4441_) == 0)
{
v___y_4445_ = v_v_4441_;
goto v___jp_4444_;
}
else
{
lean_object* v_val_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4458_; 
v_val_4450_ = lean_ctor_get(v_v_4441_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_v_4441_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4452_ = v_v_4441_;
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_val_4450_);
lean_dec(v_v_4441_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_inc(v_fvarId_4435_);
v___x_4454_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4435_, v_e_4436_, v_val_4450_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v___x_4454_);
v___x_4456_ = v___x_4452_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
v___y_4445_ = v___x_4456_;
goto v___jp_4444_;
}
}
}
v___jp_4444_:
{
size_t v___x_4446_; size_t v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = ((size_t)1ULL);
v___x_4447_ = lean_usize_add(v_i_4438_, v___x_4446_);
v___x_4448_ = lean_array_uset(v_bs_x27_4443_, v_i_4438_, v___y_4445_);
v_i_4438_ = v___x_4447_;
v_bs_4439_ = v___x_4448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4459_, lean_object* v_e_4460_, lean_object* v_sz_4461_, lean_object* v_i_4462_, lean_object* v_bs_4463_){
_start:
{
size_t v_sz_boxed_4464_; size_t v_i_boxed_4465_; lean_object* v_res_4466_; 
v_sz_boxed_4464_ = lean_unbox_usize(v_sz_4461_);
lean_dec(v_sz_4461_);
v_i_boxed_4465_ = lean_unbox_usize(v_i_4462_);
lean_dec(v_i_4462_);
v_res_4466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4459_, v_e_4460_, v_sz_boxed_4464_, v_i_boxed_4465_, v_bs_4463_);
lean_dec_ref(v_e_4460_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4467_, lean_object* v_e_4468_, size_t v_sz_4469_, size_t v_i_4470_, lean_object* v_bs_4471_){
_start:
{
uint8_t v___x_4472_; 
v___x_4472_ = lean_usize_dec_lt(v_i_4470_, v_sz_4469_);
if (v___x_4472_ == 0)
{
lean_dec(v_fvarId_4467_);
return v_bs_4471_;
}
else
{
lean_object* v_v_4473_; lean_object* v___x_4474_; lean_object* v_bs_x27_4475_; lean_object* v___x_4476_; size_t v___x_4477_; size_t v___x_4478_; lean_object* v___x_4479_; 
v_v_4473_ = lean_array_uget(v_bs_4471_, v_i_4470_);
v___x_4474_ = lean_unsigned_to_nat(0u);
v_bs_x27_4475_ = lean_array_uset(v_bs_4471_, v_i_4470_, v___x_4474_);
lean_inc(v_fvarId_4467_);
v___x_4476_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4467_, v_e_4468_, v_v_4473_);
v___x_4477_ = ((size_t)1ULL);
v___x_4478_ = lean_usize_add(v_i_4470_, v___x_4477_);
v___x_4479_ = lean_array_uset(v_bs_x27_4475_, v_i_4470_, v___x_4476_);
v_i_4470_ = v___x_4478_;
v_bs_4471_ = v___x_4479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4481_, lean_object* v_e_4482_, lean_object* v_x_4483_){
_start:
{
if (lean_obj_tag(v_x_4483_) == 0)
{
lean_object* v_cs_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4494_; 
v_cs_4484_ = lean_ctor_get(v_x_4483_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_x_4483_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4486_ = v_x_4483_;
v_isShared_4487_ = v_isSharedCheck_4494_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_cs_4484_);
lean_dec(v_x_4483_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4494_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
size_t v_sz_4488_; size_t v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v_sz_4488_ = lean_array_size(v_cs_4484_);
v___x_4489_ = ((size_t)0ULL);
v___x_4490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4481_, v_e_4482_, v_sz_4488_, v___x_4489_, v_cs_4484_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4490_);
v___x_4492_ = v___x_4486_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
lean_object* v_vs_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4505_; 
v_vs_4495_ = lean_ctor_get(v_x_4483_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_x_4483_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4497_ = v_x_4483_;
v_isShared_4498_ = v_isSharedCheck_4505_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_vs_4495_);
lean_dec(v_x_4483_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4505_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
size_t v_sz_4499_; size_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
v_sz_4499_ = lean_array_size(v_vs_4495_);
v___x_4500_ = ((size_t)0ULL);
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4481_, v_e_4482_, v_sz_4499_, v___x_4500_, v_vs_4495_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4501_);
v___x_4503_ = v___x_4497_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4506_, lean_object* v_e_4507_, lean_object* v_x_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4506_, v_e_4507_, v_x_4508_);
lean_dec_ref(v_e_4507_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4510_, lean_object* v_e_4511_, lean_object* v_sz_4512_, lean_object* v_i_4513_, lean_object* v_bs_4514_){
_start:
{
size_t v_sz_boxed_4515_; size_t v_i_boxed_4516_; lean_object* v_res_4517_; 
v_sz_boxed_4515_ = lean_unbox_usize(v_sz_4512_);
lean_dec(v_sz_4512_);
v_i_boxed_4516_ = lean_unbox_usize(v_i_4513_);
lean_dec(v_i_4513_);
v_res_4517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4510_, v_e_4511_, v_sz_boxed_4515_, v_i_boxed_4516_, v_bs_4514_);
lean_dec_ref(v_e_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4518_, lean_object* v_e_4519_, lean_object* v_t_4520_){
_start:
{
lean_object* v_root_4521_; lean_object* v_tail_4522_; lean_object* v_size_4523_; size_t v_shift_4524_; lean_object* v_tailOff_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4536_; 
v_root_4521_ = lean_ctor_get(v_t_4520_, 0);
v_tail_4522_ = lean_ctor_get(v_t_4520_, 1);
v_size_4523_ = lean_ctor_get(v_t_4520_, 2);
v_shift_4524_ = lean_ctor_get_usize(v_t_4520_, 4);
v_tailOff_4525_ = lean_ctor_get(v_t_4520_, 3);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_t_4520_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4527_ = v_t_4520_;
v_isShared_4528_ = v_isSharedCheck_4536_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_tailOff_4525_);
lean_inc(v_size_4523_);
lean_inc(v_tail_4522_);
lean_inc(v_root_4521_);
lean_dec(v_t_4520_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4536_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; size_t v_sz_4530_; size_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
lean_inc(v_fvarId_4518_);
v___x_4529_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4518_, v_e_4519_, v_root_4521_);
v_sz_4530_ = lean_array_size(v_tail_4522_);
v___x_4531_ = ((size_t)0ULL);
v___x_4532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4518_, v_e_4519_, v_sz_4530_, v___x_4531_, v_tail_4522_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v___x_4532_);
lean_ctor_set(v___x_4527_, 0, v___x_4529_);
v___x_4534_ = v___x_4527_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4535_, 2, v_size_4523_);
lean_ctor_set(v_reuseFailAlloc_4535_, 3, v_tailOff_4525_);
lean_ctor_set_usize(v_reuseFailAlloc_4535_, 4, v_shift_4524_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4537_, lean_object* v_e_4538_, lean_object* v_t_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4537_, v_e_4538_, v_t_4539_);
lean_dec_ref(v_e_4538_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4541_, lean_object* v_x_4542_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_apply_1(v_f_4541_, v_x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4544_, lean_object* v_as_4545_, lean_object* v_i_4546_, lean_object* v_acc_4547_){
_start:
{
lean_object* v___x_4548_; uint8_t v___x_4549_; 
v___x_4548_ = lean_array_get_size(v_as_4545_);
v___x_4549_ = lean_nat_dec_eq(v_i_4546_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4550_ = lean_array_fget_borrowed(v_as_4545_, v_i_4546_);
lean_inc(v_f_4544_);
lean_inc(v___x_4550_);
v___x_4551_ = lean_apply_1(v_f_4544_, v___x_4550_);
v___x_4552_ = lean_unsigned_to_nat(1u);
v___x_4553_ = lean_nat_add(v_i_4546_, v___x_4552_);
lean_dec(v_i_4546_);
v___x_4554_ = lean_array_push(v_acc_4547_, v___x_4551_);
v_i_4546_ = v___x_4553_;
v_acc_4547_ = v___x_4554_;
goto _start;
}
else
{
lean_dec(v_i_4546_);
lean_dec(v_f_4544_);
return v_acc_4547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4556_, lean_object* v_as_4557_, lean_object* v_i_4558_, lean_object* v_acc_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4556_, v_as_4557_, v_i_4558_, v_acc_4559_);
lean_dec_ref(v_as_4557_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4561_, lean_object* v_as_4562_){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4563_ = lean_unsigned_to_nat(0u);
v___x_4564_ = lean_array_get_size(v_as_4562_);
v___x_4565_ = lean_mk_empty_array_with_capacity(v___x_4564_);
v___x_4566_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4561_, v_as_4562_, v___x_4563_, v___x_4565_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4567_, lean_object* v_as_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4567_, v_as_4568_);
lean_dec_ref(v_as_4568_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4570_, size_t v_sz_4571_, size_t v_i_4572_, lean_object* v_bs_4573_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_usize_dec_lt(v_i_4572_, v_sz_4571_);
if (v___x_4574_ == 0)
{
lean_dec(v_f_4570_);
return v_bs_4573_;
}
else
{
lean_object* v_v_4575_; lean_object* v___x_4576_; lean_object* v_bs_x27_4577_; lean_object* v___y_4579_; 
v_v_4575_ = lean_array_uget(v_bs_4573_, v_i_4572_);
v___x_4576_ = lean_unsigned_to_nat(0u);
v_bs_x27_4577_ = lean_array_uset(v_bs_4573_, v_i_4572_, v___x_4576_);
switch(lean_obj_tag(v_v_4575_))
{
case 0:
{
lean_object* v_key_4584_; lean_object* v_val_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4593_; 
v_key_4584_ = lean_ctor_get(v_v_4575_, 0);
v_val_4585_ = lean_ctor_get(v_v_4575_, 1);
v_isSharedCheck_4593_ = !lean_is_exclusive(v_v_4575_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4587_ = v_v_4575_;
v_isShared_4588_ = v_isSharedCheck_4593_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_val_4585_);
lean_inc(v_key_4584_);
lean_dec(v_v_4575_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4593_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
lean_inc(v_f_4570_);
v___x_4589_ = lean_apply_1(v_f_4570_, v_val_4585_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 1, v___x_4589_);
v___x_4591_ = v___x_4587_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_key_4584_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v___x_4589_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
v___y_4579_ = v___x_4591_;
goto v___jp_4578_;
}
}
}
case 1:
{
lean_object* v_node_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4602_; 
v_node_4594_ = lean_ctor_get(v_v_4575_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_v_4575_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4596_ = v_v_4575_;
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_node_4594_);
lean_dec(v_v_4575_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4600_; 
lean_inc(v_f_4570_);
v___x_4598_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4570_, v_node_4594_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4598_);
v___x_4600_ = v___x_4596_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
v___y_4579_ = v___x_4600_;
goto v___jp_4578_;
}
}
}
default: 
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_box(2);
v___y_4579_ = v___x_4603_;
goto v___jp_4578_;
}
}
v___jp_4578_:
{
size_t v___x_4580_; size_t v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = ((size_t)1ULL);
v___x_4581_ = lean_usize_add(v_i_4572_, v___x_4580_);
v___x_4582_ = lean_array_uset(v_bs_x27_4577_, v_i_4572_, v___y_4579_);
v_i_4572_ = v___x_4581_;
v_bs_4573_ = v___x_4582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4604_, lean_object* v_n_4605_){
_start:
{
if (lean_obj_tag(v_n_4605_) == 0)
{
lean_object* v_es_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4616_; 
v_es_4606_ = lean_ctor_get(v_n_4605_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v_n_4605_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4608_ = v_n_4605_;
v_isShared_4609_ = v_isSharedCheck_4616_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_es_4606_);
lean_dec(v_n_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4616_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
size_t v_sz_4610_; size_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v_sz_4610_ = lean_array_size(v_es_4606_);
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4604_, v_sz_4610_, v___x_4611_, v_es_4606_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4612_);
v___x_4614_ = v___x_4608_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
else
{
lean_object* v_ks_4617_; lean_object* v_vs_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4626_; 
v_ks_4617_ = lean_ctor_get(v_n_4605_, 0);
v_vs_4618_ = lean_ctor_get(v_n_4605_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_n_4605_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4620_ = v_n_4605_;
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_vs_4618_);
lean_inc(v_ks_4617_);
lean_dec(v_n_4605_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_val_4622_; lean_object* v___x_4624_; 
v_val_4622_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4604_, v_vs_4618_);
lean_dec_ref(v_vs_4618_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v_val_4622_);
v___x_4624_ = v___x_4620_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_ks_4617_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_val_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4627_, lean_object* v_sz_4628_, lean_object* v_i_4629_, lean_object* v_bs_4630_){
_start:
{
size_t v_sz_boxed_4631_; size_t v_i_boxed_4632_; lean_object* v_res_4633_; 
v_sz_boxed_4631_ = lean_unbox_usize(v_sz_4628_);
lean_dec(v_sz_4628_);
v_i_boxed_4632_ = lean_unbox_usize(v_i_4629_);
lean_dec(v_i_4629_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4627_, v_sz_boxed_4631_, v_i_boxed_4632_, v_bs_4630_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4634_, lean_object* v_f_4635_){
_start:
{
lean_object* v___f_4636_; lean_object* v___x_4637_; 
v___f_4636_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4636_, 0, v_f_4635_);
v___x_4637_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4636_, v_pm_4634_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4638_, lean_object* v_e_4639_, lean_object* v_lctx_4640_){
_start:
{
lean_object* v_lctx_4641_; lean_object* v_fvarIdToDecl_4642_; lean_object* v_decls_4643_; lean_object* v_auxDeclToFullName_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4654_; 
v_lctx_4641_ = l_Lean_LocalContext_erase(v_lctx_4640_, v_fvarId_4638_);
v_fvarIdToDecl_4642_ = lean_ctor_get(v_lctx_4641_, 0);
v_decls_4643_ = lean_ctor_get(v_lctx_4641_, 1);
v_auxDeclToFullName_4644_ = lean_ctor_get(v_lctx_4641_, 2);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_lctx_4641_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4646_ = v_lctx_4641_;
v_isShared_4647_ = v_isSharedCheck_4654_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_auxDeclToFullName_4644_);
lean_inc(v_decls_4643_);
lean_inc(v_fvarIdToDecl_4642_);
lean_dec(v_lctx_4641_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4654_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___f_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4652_; 
lean_inc_ref(v_e_4639_);
lean_inc(v_fvarId_4638_);
v___f_4648_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4648_, 0, v_fvarId_4638_);
lean_closure_set(v___f_4648_, 1, v_e_4639_);
v___x_4649_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4642_, v___f_4648_);
v___x_4650_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4638_, v_e_4639_, v_decls_4643_);
lean_dec_ref(v_e_4639_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 1, v___x_4650_);
lean_ctor_set(v___x_4646_, 0, v___x_4649_);
v___x_4652_ = v___x_4646_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4650_);
lean_ctor_set(v_reuseFailAlloc_4653_, 2, v_auxDeclToFullName_4644_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4655_, lean_object* v_00_u03c3_4656_, lean_object* v_pm_4657_, lean_object* v_f_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4657_, v_f_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4660_, lean_object* v_f_4661_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4661_, v_pm_4660_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4663_, lean_object* v_00_u03c3_4664_, lean_object* v_pm_4665_, lean_object* v_f_4666_){
_start:
{
lean_object* v___x_4667_; 
v___x_4667_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4666_, v_pm_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4668_, lean_object* v_00_u03b2_4669_, lean_object* v_00_u03c3_4670_, lean_object* v_f_4671_, lean_object* v_n_4672_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4671_, v_n_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4674_, lean_object* v_00_u03b2_4675_, lean_object* v_00_u03c3_4676_, lean_object* v_f_4677_, size_t v_sz_4678_, size_t v_i_4679_, lean_object* v_bs_4680_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4677_, v_sz_4678_, v_i_4679_, v_bs_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4682_, lean_object* v_00_u03b2_4683_, lean_object* v_00_u03c3_4684_, lean_object* v_f_4685_, lean_object* v_sz_4686_, lean_object* v_i_4687_, lean_object* v_bs_4688_){
_start:
{
size_t v_sz_boxed_4689_; size_t v_i_boxed_4690_; lean_object* v_res_4691_; 
v_sz_boxed_4689_ = lean_unbox_usize(v_sz_4686_);
lean_dec(v_sz_4686_);
v_i_boxed_4690_ = lean_unbox_usize(v_i_4687_);
lean_dec(v_i_4687_);
v_res_4691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4682_, v_00_u03b2_4683_, v_00_u03c3_4684_, v_f_4685_, v_sz_boxed_4689_, v_i_boxed_4690_, v_bs_4688_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4692_, lean_object* v_00_u03b2_4693_, lean_object* v_f_4694_, lean_object* v_as_4695_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4694_, v_as_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4697_, lean_object* v_00_u03b2_4698_, lean_object* v_f_4699_, lean_object* v_as_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4697_, v_00_u03b2_4698_, v_f_4699_, v_as_4700_);
lean_dec_ref(v_as_4700_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4702_, lean_object* v_00_u03b2_4703_, lean_object* v_f_4704_, lean_object* v_as_4705_, lean_object* v_i_4706_, lean_object* v_acc_4707_, lean_object* v_hle_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4704_, v_as_4705_, v_i_4706_, v_acc_4707_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4710_, lean_object* v_00_u03b2_4711_, lean_object* v_f_4712_, lean_object* v_as_4713_, lean_object* v_i_4714_, lean_object* v_acc_4715_, lean_object* v_hle_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4710_, v_00_u03b2_4711_, v_f_4712_, v_as_4713_, v_i_4714_, v_acc_4715_, v_hle_4716_);
lean_dec_ref(v_as_4713_);
return v_res_4717_;
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
