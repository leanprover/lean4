// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Theorems
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic public import Init.Data.Range.Polymorphic.RangeIterator import Lean.Meta.Eqns import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadEnvMetaM;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_getConstVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Grind.Origin.decl"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__4;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Grind.Origin.fvar"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Grind.Origin.stx"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Grind.Origin.local"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprOrigin_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprOrigin = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqOrigin = (const lean_object*)&l_Lean_Meta_Grind_instBEqOrigin___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHashableOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHashableOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHashableOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHashableOrigin = (const lean_object*)&l_Lean_Meta_Grind_instHashableOrigin___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Tactic.Grind.Theorems"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.Theorems.insert"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` is not marked with the `[grind]` attribute"};
static const lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getProofForDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid `grind` theorem `"};
static const lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getProofForDecl___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofForDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__1;
static const lean_string_object l_Lean_Meta_Grind_getProofForDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`, type is not a proposition"};
static const lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getProofForDecl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofForDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_Origin_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
lean_object* v_id_7_; lean_object* v_ref_8_; lean_object* v___x_9_; 
v_id_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_id_7_);
v_ref_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_ref_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_id_7_, v_ref_8_);
return v___x_9_;
}
else
{
lean_object* v_declName_10_; lean_object* v___x_11_; 
v_declName_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_declName_10_);
lean_dec_ref(v_t_5_);
v___x_11_ = lean_apply_1(v_k_6_, v_declName_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_Grind_Origin_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim___redArg(lean_object* v_t_24_, lean_object* v_decl_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_24_, v_decl_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_decl_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_28_, v_decl_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim___redArg(lean_object* v_t_32_, lean_object* v_fvar_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_32_, v_fvar_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_fvar_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_36_, v_fvar_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim___redArg(lean_object* v_t_40_, lean_object* v_stx_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_40_, v_stx_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_stx_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_44_, v_stx_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim___redArg(lean_object* v_t_48_, lean_object* v_local_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_48_, v_local_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_local_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_52_, v_local_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(2u);
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
switch(lean_obj_tag(v_x_88_))
{
case 0:
{
lean_object* v_declName_90_; lean_object* v___y_92_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_declName_90_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_declName_90_);
lean_dec_ref_known(v_x_88_, 1);
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_89_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_92_ = v___x_103_;
goto v___jp_91_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_93_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__2));
v___x_94_ = lean_unsigned_to_nat(1024u);
v___x_95_ = l_Lean_Name_reprPrec(v_declName_90_, v___x_94_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_inc(v___y_92_);
v___x_97_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_97_, 0, v___y_92_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = 0;
v___x_99_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_98_);
v___x_100_ = l_Repr_addAppParen(v___x_99_, v_prec_89_);
return v___x_100_;
}
}
case 1:
{
lean_object* v_fvarId_105_; lean_object* v___y_107_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_fvarId_105_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_fvarId_105_);
lean_dec_ref_known(v_x_88_, 1);
v___x_116_ = lean_unsigned_to_nat(1024u);
v___x_117_ = lean_nat_dec_le(v___x_116_, v_prec_89_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_107_ = v___x_118_;
goto v___jp_106_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__7));
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = l_Lean_Name_reprPrec(v_fvarId_105_, v___x_109_);
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_108_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
lean_inc(v___y_107_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_89_);
return v___x_115_;
}
}
case 2:
{
lean_object* v_id_120_; lean_object* v_ref_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_145_; 
v_id_120_ = lean_ctor_get(v_x_88_, 0);
v_ref_121_ = lean_ctor_get(v_x_88_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_145_ == 0)
{
v___x_123_ = v_x_88_;
v_isShared_124_ = v_isSharedCheck_145_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_ref_121_);
lean_inc(v_id_120_);
lean_dec(v_x_88_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_145_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___y_126_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_89_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_126_ = v___x_143_;
goto v___jp_125_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_126_ = v___x_144_;
goto v___jp_125_;
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_127_ = lean_box(1);
v___x_128_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__10));
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = l_Lean_Name_reprPrec(v_id_120_, v___x_129_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 5);
lean_ctor_set(v___x_123_, 1, v___x_130_);
lean_ctor_set(v___x_123_, 0, v___x_128_);
v___x_132_ = v___x_123_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_140_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_127_);
v___x_134_ = l_Lean_Syntax_instRepr_repr(v_ref_121_, v___x_129_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_inc(v___y_126_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_126_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_89_);
return v___x_139_;
}
}
}
}
default: 
{
lean_object* v_id_146_; lean_object* v___y_148_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_id_146_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_id_146_);
lean_dec_ref_known(v_x_88_, 1);
v___x_157_ = lean_unsigned_to_nat(1024u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v_prec_89_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_148_ = v___x_159_;
goto v___jp_147_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_148_ = v___x_160_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_149_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__13));
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = l_Lean_Name_reprPrec(v_id_146_, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
lean_inc(v___y_148_);
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___y_148_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___x_156_ = l_Repr_addAppParen(v___x_155_, v_prec_89_);
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___boxed(lean_object* v_x_161_, lean_object* v_prec_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Grind_instReprOrigin_repr(v_x_161_, v_prec_162_);
lean_dec(v_prec_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object* v_x_166_){
_start:
{
lean_object* v_declName_167_; 
v_declName_167_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_declName_167_);
return v_declName_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Meta_Grind_Origin_key(v_x_168_);
lean_dec_ref(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object* v_o_170_){
_start:
{
switch(lean_obj_tag(v_o_170_))
{
case 0:
{
lean_object* v_declName_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v_declName_171_ = lean_ctor_get(v_o_170_, 0);
lean_inc(v_declName_171_);
lean_dec_ref_known(v_o_170_, 1);
v___x_172_ = 0;
v___x_173_ = l_Lean_MessageData_ofConstName(v_declName_171_, v___x_172_);
return v___x_173_;
}
case 1:
{
lean_object* v_fvarId_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_fvarId_174_ = lean_ctor_get(v_o_170_, 0);
lean_inc(v_fvarId_174_);
lean_dec_ref_known(v_o_170_, 1);
v___x_175_ = l_Lean_mkFVar(v_fvarId_174_);
v___x_176_ = l_Lean_MessageData_ofExpr(v___x_175_);
return v___x_176_;
}
case 2:
{
lean_object* v_ref_177_; lean_object* v___x_178_; 
v_ref_177_ = lean_ctor_get(v_o_170_, 1);
lean_inc(v_ref_177_);
lean_dec_ref_known(v_o_170_, 2);
v___x_178_ = l_Lean_MessageData_ofSyntax(v_ref_177_);
return v___x_178_;
}
default: 
{
lean_object* v_id_179_; lean_object* v___x_180_; 
v_id_179_ = lean_ctor_get(v_o_170_, 0);
lean_inc(v_id_179_);
lean_dec_ref_known(v_o_170_, 1);
v___x_180_ = l_Lean_MessageData_ofName(v_id_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin___lam__0(lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___y_184_; lean_object* v_declName_187_; 
v_declName_187_ = lean_ctor_get(v_a_181_, 0);
v___y_184_ = v_declName_187_;
goto v___jp_183_;
v___jp_183_:
{
lean_object* v_declName_185_; uint8_t v___x_186_; 
v_declName_185_ = lean_ctor_get(v_b_182_, 0);
v___x_186_ = lean_name_eq(v___y_184_, v_declName_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_Meta_Grind_instBEqOrigin___lam__0(v_a_188_, v_b_189_);
lean_dec_ref(v_b_189_);
lean_dec_ref(v_a_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object* v_a_194_){
_start:
{
lean_object* v___y_196_; lean_object* v_declName_199_; 
v_declName_199_ = lean_ctor_get(v_a_194_, 0);
v___y_196_ = v_declName_199_;
goto v___jp_195_;
v___jp_195_:
{
if (lean_obj_tag(v___y_196_) == 0)
{
uint64_t v___x_197_; 
v___x_197_ = 1723ULL;
return v___x_197_;
}
else
{
uint64_t v_hash_198_; 
v_hash_198_ = lean_ctor_get_uint64(v___y_196_, sizeof(void*)*2);
return v_hash_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object* v_a_200_){
_start:
{
uint64_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lean_Meta_Grind_instHashableOrigin___lam__0(v_a_200_);
lean_dec_ref(v_a_200_);
v_r_202_ = lean_box_uint64(v_res_201_);
return v_r_202_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___boxed(lean_object* v___dummy_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
return v_res_211_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_object* v_00_u03b2_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
v___x_218_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0);
v___x_219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_217_);
lean_ctor_set(v___x_219_, 3, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg(){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___boxed(lean_object* v___dummy_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v_res_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object* v_00_u03b1_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg(){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Meta_Grind_instInhabitedTheorems___redArg();
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems(lean_object* v_a_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
v___x_253_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9));
v___x_254_ = l_instInhabitedOfMonad___redArg(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13));
v___x_259_ = lean_unsigned_to_nat(6u);
v___x_260_ = lean_unsigned_to_nat(83u);
v___x_261_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12));
v___x_262_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11));
v___x_263_ = l_mkPanicMessageWithDecl(v___x_262_, v___x_261_, v___x_260_, v___x_259_, v___x_258_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg(lean_object* v_inst_266_, lean_object* v_s_267_, lean_object* v_thm_268_){
_start:
{
lean_object* v_getSymbols_269_; lean_object* v_setSymbols_270_; lean_object* v_getOrigin_271_; lean_object* v___x_272_; lean_object* v___x_276_; 
v_getSymbols_269_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_getSymbols_269_);
v_setSymbols_270_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_setSymbols_270_);
v_getOrigin_271_ = lean_ctor_get(v_inst_266_, 2);
lean_inc_ref(v_getOrigin_271_);
lean_dec_ref(v_inst_266_);
v___x_272_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10);
lean_inc(v_thm_268_);
v___x_276_ = lean_apply_1(v_getSymbols_269_, v_thm_268_);
if (lean_obj_tag(v___x_276_) == 1)
{
lean_object* v_head_277_; 
v_head_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_head_277_);
if (lean_obj_tag(v_head_277_) == 2)
{
lean_object* v_tail_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_326_; 
v_tail_278_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_327_);
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_326_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_tail_278_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_326_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_constName_282_; lean_object* v_smap_283_; lean_object* v_origins_284_; lean_object* v_erased_285_; lean_object* v_omap_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_325_; 
v_constName_282_ = lean_ctor_get(v_head_277_, 0);
lean_inc(v_constName_282_);
lean_dec_ref_known(v_head_277_, 1);
v_smap_283_ = lean_ctor_get(v_s_267_, 0);
v_origins_284_ = lean_ctor_get(v_s_267_, 1);
v_erased_285_ = lean_ctor_get(v_s_267_, 2);
v_omap_286_ = lean_ctor_get(v_s_267_, 3);
v_isSharedCheck_325_ = !lean_is_exclusive(v_s_267_);
if (v_isSharedCheck_325_ == 0)
{
v___x_288_ = v_s_267_;
v_isShared_289_ = v_isSharedCheck_325_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_omap_286_);
lean_inc(v_erased_285_);
lean_inc(v_origins_284_);
lean_inc(v_smap_283_);
lean_dec(v_s_267_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_325_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_thm_294_; lean_object* v_origin_295_; lean_object* v___x_296_; lean_object* v_origins_297_; lean_object* v_erased_298_; lean_object* v___y_300_; lean_object* v___x_318_; 
v___f_290_ = ((lean_object*)(l_Lean_Meta_Grind_instBEqOrigin___closed__0));
v___f_291_ = ((lean_object*)(l_Lean_Meta_Grind_instHashableOrigin___closed__0));
v___x_292_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
v_thm_294_ = lean_apply_2(v_setSymbols_270_, v_thm_268_, v_tail_278_);
lean_inc(v_thm_294_);
v_origin_295_ = lean_apply_1(v_getOrigin_271_, v_thm_294_);
v___x_296_ = lean_box(0);
lean_inc_ref_n(v_origin_295_, 2);
v_origins_297_ = l_Lean_PersistentHashMap_insert___redArg(v___f_290_, v___f_291_, v_origins_284_, v_origin_295_, v___x_296_);
v_erased_298_ = l_Lean_PersistentHashMap_erase___redArg(v___f_290_, v___f_291_, v_erased_285_, v_origin_295_);
lean_inc(v_constName_282_);
v___x_318_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_292_, v___x_293_, v_smap_283_, v_constName_282_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v___x_318_, 1);
lean_inc(v_thm_294_);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v_thm_294_);
lean_ctor_set(v___x_320_, 1, v_val_319_);
v___x_321_ = l_Lean_PersistentHashMap_insert___redArg(v___x_292_, v___x_293_, v_smap_283_, v_constName_282_, v___x_320_);
v___y_300_ = v___x_321_;
goto v___jp_299_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
lean_inc(v_thm_294_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v_thm_294_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_PersistentHashMap_insert___redArg(v___x_292_, v___x_293_, v_smap_283_, v_constName_282_, v___x_323_);
v___y_300_ = v___x_324_;
goto v___jp_299_;
}
v___jp_299_:
{
lean_object* v___x_301_; 
lean_inc_ref(v_origin_295_);
v___x_301_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_290_, v___f_291_, v_omap_286_, v_origin_295_);
if (lean_obj_tag(v___x_301_) == 1)
{
lean_object* v_val_302_; lean_object* v___x_304_; 
v_val_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_val_302_);
lean_dec_ref_known(v___x_301_, 1);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_val_302_);
lean_ctor_set(v___x_280_, 0, v_thm_294_);
v___x_304_ = v___x_280_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_thm_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_val_302_);
v___x_304_ = v_reuseFailAlloc_309_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_PersistentHashMap_insert___redArg(v___f_290_, v___f_291_, v_omap_286_, v_origin_295_, v___x_304_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v___x_305_);
lean_ctor_set(v___x_288_, 2, v_erased_298_);
lean_ctor_set(v___x_288_, 1, v_origins_297_);
lean_ctor_set(v___x_288_, 0, v___y_300_);
v___x_307_ = v___x_288_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___y_300_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_origins_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_erased_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v___x_301_);
v___x_310_ = lean_box(0);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_310_);
lean_ctor_set(v___x_280_, 0, v_thm_294_);
v___x_312_ = v___x_280_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_thm_294_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_317_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Lean_PersistentHashMap_insert___redArg(v___f_290_, v___f_291_, v_omap_286_, v_origin_295_, v___x_312_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v___x_313_);
lean_ctor_set(v___x_288_, 2, v_erased_298_);
lean_ctor_set(v___x_288_, 1, v_origins_297_);
lean_ctor_set(v___x_288_, 0, v___y_300_);
v___x_315_ = v___x_288_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___y_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_origins_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_erased_298_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
else
{
lean_dec(v_head_277_);
lean_dec_ref_known(v___x_276_, 2);
lean_dec_ref(v_getOrigin_271_);
lean_dec(v_setSymbols_270_);
lean_dec(v_thm_268_);
lean_dec_ref(v_s_267_);
goto v___jp_273_;
}
}
else
{
lean_dec(v___x_276_);
lean_dec_ref(v_getOrigin_271_);
lean_dec(v_setSymbols_270_);
lean_dec(v_thm_268_);
lean_dec_ref(v_s_267_);
goto v___jp_273_;
}
v___jp_273_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14);
v___x_275_ = l_panic___redArg(v___x_272_, v___x_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_s_330_, lean_object* v_thm_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_329_, v_s_330_, v_thm_331_);
return v___x_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_333_, lean_object* v_i_334_, lean_object* v_k_335_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___y_339_; lean_object* v___y_340_; 
v___x_336_ = lean_array_get_size(v_keys_333_);
v___x_337_ = lean_nat_dec_lt(v_i_334_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec(v_i_334_);
return v___x_337_;
}
else
{
lean_object* v_k_x27_345_; lean_object* v___y_347_; lean_object* v_declName_349_; 
v_k_x27_345_ = lean_array_fget_borrowed(v_keys_333_, v_i_334_);
v_declName_349_ = lean_ctor_get(v_k_335_, 0);
v___y_347_ = v_declName_349_;
goto v___jp_346_;
v___jp_346_:
{
lean_object* v_declName_348_; 
v_declName_348_ = lean_ctor_get(v_k_x27_345_, 0);
v___y_339_ = v___y_347_;
v___y_340_ = v_declName_348_;
goto v___jp_338_;
}
}
v___jp_338_:
{
uint8_t v___x_341_; 
v___x_341_ = lean_name_eq(v___y_339_, v___y_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_334_, v___x_342_);
lean_dec(v_i_334_);
v_i_334_ = v___x_343_;
goto _start;
}
else
{
lean_dec(v_i_334_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_350_, lean_object* v_i_351_, lean_object* v_k_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_350_, v_i_351_, v_k_352_);
lean_dec_ref(v_k_352_);
lean_dec_ref(v_keys_350_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_es_358_; lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v_j_362_; lean_object* v___x_363_; 
v_es_358_ = lean_ctor_get(v_x_355_, 0);
v___x_359_ = lean_box(2);
v___x_360_ = ((size_t)31ULL);
v___x_361_ = lean_usize_land(v_x_356_, v___x_360_);
v_j_362_ = lean_usize_to_nat(v___x_361_);
v___x_363_ = lean_array_get_borrowed(v___x_359_, v_es_358_, v_j_362_);
lean_dec(v_j_362_);
switch(lean_obj_tag(v___x_363_))
{
case 0:
{
lean_object* v_key_364_; lean_object* v___y_366_; lean_object* v_declName_369_; 
v_key_364_ = lean_ctor_get(v___x_363_, 0);
v_declName_369_ = lean_ctor_get(v_x_357_, 0);
v___y_366_ = v_declName_369_;
goto v___jp_365_;
v___jp_365_:
{
lean_object* v_declName_367_; uint8_t v___x_368_; 
v_declName_367_ = lean_ctor_get(v_key_364_, 0);
v___x_368_ = lean_name_eq(v___y_366_, v_declName_367_);
return v___x_368_;
}
}
case 1:
{
lean_object* v_node_370_; size_t v___x_371_; size_t v___x_372_; 
v_node_370_ = lean_ctor_get(v___x_363_, 0);
v___x_371_ = ((size_t)5ULL);
v___x_372_ = lean_usize_shift_right(v_x_356_, v___x_371_);
v_x_355_ = v_node_370_;
v_x_356_ = v___x_372_;
goto _start;
}
default: 
{
uint8_t v___x_374_; 
v___x_374_ = 0;
return v___x_374_;
}
}
}
else
{
lean_object* v_ks_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_ks_375_ = lean_ctor_get(v_x_355_, 0);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_ks_375_, v___x_376_, v_x_357_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
size_t v_x_203__boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_x_203__boxed_381_ = lean_unbox_usize(v_x_379_);
lean_dec(v_x_379_);
v_res_382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_378_, v_x_203__boxed_381_, v_x_380_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_x_378_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint64_t v___y_387_; lean_object* v___y_391_; lean_object* v_declName_394_; 
v_declName_394_ = lean_ctor_get(v_x_385_, 0);
v___y_391_ = v_declName_394_;
goto v___jp_390_;
v___jp_386_:
{
size_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = lean_uint64_to_usize(v___y_387_);
v___x_389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_384_, v___x_388_, v_x_385_);
return v___x_389_;
}
v___jp_390_:
{
if (lean_obj_tag(v___y_391_) == 0)
{
uint64_t v___x_392_; 
v___x_392_ = 1723ULL;
v___y_387_ = v___x_392_;
goto v___jp_386_;
}
else
{
uint64_t v_hash_393_; 
v_hash_393_ = lean_ctor_get_uint64(v___y_391_, sizeof(void*)*2);
v___y_387_ = v_hash_393_;
goto v___jp_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_395_, v_x_396_);
lean_dec_ref(v_x_396_);
lean_dec_ref(v_x_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object* v_s_399_, lean_object* v_origin_400_){
_start:
{
lean_object* v_origins_401_; uint8_t v___x_402_; 
v_origins_401_ = lean_ctor_get(v_s_399_, 1);
v___x_402_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_origins_401_, v_origin_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object* v_s_403_, lean_object* v_origin_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_403_, v_origin_404_);
lean_dec_ref(v_origin_404_);
lean_dec_ref(v_s_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object* v_00_u03b1_407_, lean_object* v_s_408_, lean_object* v_origin_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_408_, v_origin_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object* v_00_u03b1_411_, lean_object* v_s_412_, lean_object* v_origin_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Lean_Meta_Grind_Theorems_contains(v_00_u03b1_411_, v_s_412_, v_origin_413_);
lean_dec_ref(v_origin_413_);
lean_dec_ref(v_s_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(v_00_u03b2_420_, v_x_421_, v_x_422_);
lean_dec_ref(v_x_422_);
lean_dec_ref(v_x_421_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_x_426_, size_t v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_426_, v_x_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_301__boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_x_301__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(v_00_u03b2_430_, v_x_431_, v_x_301__boxed_434_, v_x_433_);
lean_dec_ref(v_x_433_);
lean_dec_ref(v_x_431_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_437_, lean_object* v_keys_438_, lean_object* v_vals_439_, lean_object* v_heq_440_, lean_object* v_i_441_, lean_object* v_k_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_438_, v_i_441_, v_k_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_444_, lean_object* v_keys_445_, lean_object* v_vals_446_, lean_object* v_heq_447_, lean_object* v_i_448_, lean_object* v_k_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(v_00_u03b2_444_, v_keys_445_, v_vals_446_, v_heq_447_, v_i_448_, v_k_449_);
lean_dec_ref(v_k_449_);
lean_dec_ref(v_vals_446_);
lean_dec_ref(v_keys_445_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_452_, lean_object* v_v_453_, lean_object* v_i_454_){
_start:
{
lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_464_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_array_get_size(v_xs_452_);
v___x_467_ = lean_nat_dec_lt(v_i_454_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v_i_454_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v_declName_470_; 
v___x_469_ = lean_array_fget_borrowed(v_xs_452_, v_i_454_);
v_declName_470_ = lean_ctor_get(v___x_469_, 0);
v___y_464_ = v_declName_470_;
goto v___jp_463_;
}
v___jp_455_:
{
uint8_t v___x_458_; 
v___x_458_ = lean_name_eq(v___y_456_, v___y_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_i_454_, v___x_459_);
lean_dec(v_i_454_);
v_i_454_ = v___x_460_;
goto _start;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_i_454_);
return v___x_462_;
}
}
v___jp_463_:
{
lean_object* v_declName_465_; 
v_declName_465_ = lean_ctor_get(v_v_453_, 0);
v___y_456_ = v___y_464_;
v___y_457_ = v_declName_465_;
goto v___jp_455_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_471_, lean_object* v_v_472_, lean_object* v_i_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_471_, v_v_472_, v_i_473_);
lean_dec_ref(v_v_472_);
lean_dec_ref(v_xs_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object* v_xs_475_, lean_object* v_v_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_475_, v_v_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_479_, lean_object* v_v_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_xs_479_, v_v_480_);
lean_dec_ref(v_v_480_);
lean_dec_ref(v_xs_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_es_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v_j_489_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_entry_503_; 
v_es_485_ = lean_ctor_get(v_x_482_, 0);
v___x_486_ = lean_box(2);
v___x_487_ = ((size_t)31ULL);
v___x_488_ = lean_usize_land(v_x_483_, v___x_487_);
v_j_489_ = lean_usize_to_nat(v___x_488_);
v_entry_503_ = lean_array_get(v___x_486_, v_es_485_, v_j_489_);
switch(lean_obj_tag(v_entry_503_))
{
case 0:
{
lean_object* v_key_504_; lean_object* v___y_506_; lean_object* v_declName_508_; 
v_key_504_ = lean_ctor_get(v_entry_503_, 0);
lean_inc(v_key_504_);
lean_dec_ref_known(v_entry_503_, 2);
v_declName_508_ = lean_ctor_get(v_x_484_, 0);
v___y_506_ = v_declName_508_;
goto v___jp_505_;
v___jp_505_:
{
lean_object* v_declName_507_; 
v_declName_507_ = lean_ctor_get(v_key_504_, 0);
lean_inc(v_declName_507_);
lean_dec(v_key_504_);
v___y_491_ = v___y_506_;
v___y_492_ = v_declName_507_;
goto v___jp_490_;
}
}
case 1:
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_543_; 
lean_inc_ref(v_es_485_);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_544_);
v___x_510_ = v_x_482_;
v_isShared_511_ = v_isSharedCheck_543_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_x_482_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_543_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_node_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_542_; 
v_node_512_ = lean_ctor_get(v_entry_503_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_entry_503_);
if (v_isSharedCheck_542_ == 0)
{
v___x_514_ = v_entry_503_;
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_node_512_);
lean_dec(v_entry_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_542_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
size_t v___x_516_; lean_object* v_entries_517_; size_t v___x_518_; lean_object* v_newNode_519_; lean_object* v___x_520_; 
v___x_516_ = ((size_t)5ULL);
v_entries_517_ = lean_array_set(v_es_485_, v_j_489_, v___x_486_);
v___x_518_ = lean_usize_shift_right(v_x_483_, v___x_516_);
v_newNode_519_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_node_512_, v___x_518_, v_x_484_);
lean_inc_ref(v_newNode_519_);
v___x_520_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v_newNode_519_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_newNode_519_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_array_set(v_entries_517_, v_j_489_, v___x_522_);
lean_dec(v_j_489_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_523_);
v___x_525_ = v___x_510_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_val_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_newNode_519_);
lean_del_object(v___x_514_);
v_val_528_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v___x_520_, 1);
v_fst_529_ = lean_ctor_get(v_val_528_, 0);
v_snd_530_ = lean_ctor_get(v_val_528_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_val_528_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v_val_528_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_529_);
lean_dec(v_val_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_529_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_snd_530_);
v___x_535_ = v_reuseFailAlloc_540_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_set(v_entries_517_, v_j_489_, v___x_535_);
lean_dec(v_j_489_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_536_);
v___x_538_ = v___x_510_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_489_);
return v_x_482_;
}
}
v___jp_490_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_name_eq(v___y_491_, v___y_492_);
lean_dec(v___y_492_);
if (v___x_493_ == 0)
{
lean_dec(v_j_489_);
return v_x_482_;
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_es_485_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_502_);
v___x_495_ = v_x_482_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_482_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_array_set(v_es_485_, v_j_489_, v___x_486_);
lean_dec(v_j_489_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
else
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_560_; 
v_ks_545_ = lean_ctor_get(v_x_482_, 0);
v_vs_546_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_560_ == 0)
{
v___x_548_ = v_x_482_;
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_vs_546_);
lean_inc(v_ks_545_);
lean_dec(v_x_482_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_ks_545_, v_x_484_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_552_; 
if (v_isShared_549_ == 0)
{
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_ks_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vs_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_val_554_; lean_object* v_keys_x27_555_; lean_object* v_vals_x27_556_; lean_object* v___x_558_; 
v_val_554_ = lean_ctor_get(v___x_550_, 0);
lean_inc_n(v_val_554_, 2);
lean_dec_ref_known(v___x_550_, 1);
v_keys_x27_555_ = l_Array_eraseIdx___redArg(v_ks_545_, v_val_554_);
v_vals_x27_556_ = l_Array_eraseIdx___redArg(v_vs_546_, v_val_554_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_vals_x27_556_);
lean_ctor_set(v___x_548_, 0, v_keys_x27_555_);
v___x_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_keys_x27_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vals_x27_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
size_t v_x_603__boxed_564_; lean_object* v_res_565_; 
v_x_603__boxed_564_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_565_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_561_, v_x_603__boxed_564_, v_x_563_);
lean_dec_ref(v_x_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint64_t v___y_569_; lean_object* v___y_573_; lean_object* v_declName_576_; 
v_declName_576_ = lean_ctor_get(v_x_567_, 0);
v___y_573_ = v_declName_576_;
goto v___jp_572_;
v___jp_568_:
{
size_t v_h_570_; lean_object* v___x_571_; 
v_h_570_ = lean_uint64_to_usize(v___y_569_);
v___x_571_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_566_, v_h_570_, v_x_567_);
return v___x_571_;
}
v___jp_572_:
{
if (lean_obj_tag(v___y_573_) == 0)
{
uint64_t v___x_574_; 
v___x_574_ = 1723ULL;
v___y_569_ = v___x_574_;
goto v___jp_568_;
}
else
{
uint64_t v_hash_575_; 
v_hash_575_ = lean_ctor_get_uint64(v___y_573_, sizeof(void*)*2);
v___y_569_ = v_hash_575_;
goto v___jp_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_577_, v_x_578_);
lean_dec_ref(v_x_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v_ks_584_; lean_object* v_vs_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_614_; 
v_ks_584_ = lean_ctor_get(v_x_580_, 0);
v_vs_585_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_614_ == 0)
{
v___x_587_ = v_x_580_;
v_isShared_588_ = v_isSharedCheck_614_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_vs_585_);
lean_inc(v_ks_584_);
lean_dec(v_x_580_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_614_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_ks_584_);
v___x_605_ = lean_nat_dec_lt(v_x_581_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_587_);
lean_dec(v_x_581_);
v___x_606_ = lean_array_push(v_ks_584_, v_x_582_);
v___x_607_ = lean_array_push(v_vs_585_, v_x_583_);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_k_x27_609_; lean_object* v___y_611_; lean_object* v_declName_613_; 
v_k_x27_609_ = lean_array_fget_borrowed(v_ks_584_, v_x_581_);
v_declName_613_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_declName_613_);
v___y_611_ = v_declName_613_;
goto v___jp_610_;
v___jp_610_:
{
lean_object* v_declName_612_; 
v_declName_612_ = lean_ctor_get(v_k_x27_609_, 0);
lean_inc(v_declName_612_);
v___y_590_ = v___y_611_;
v___y_591_ = v_declName_612_;
goto v___jp_589_;
}
}
v___jp_589_:
{
uint8_t v___x_592_; 
v___x_592_ = lean_name_eq(v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
if (v_isShared_588_ == 0)
{
v___x_594_ = v___x_587_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ks_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_vs_585_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_x_581_, v___x_595_);
lean_dec(v_x_581_);
v_x_580_ = v___x_594_;
v_x_581_ = v___x_596_;
goto _start;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = lean_array_fset(v_ks_584_, v_x_581_, v_x_582_);
v___x_600_ = lean_array_fset(v_vs_585_, v_x_581_, v_x_583_);
lean_dec(v_x_581_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_600_);
lean_ctor_set(v___x_587_, 0, v___x_599_);
v___x_602_ = v___x_587_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object* v_n_615_, lean_object* v_k_616_, lean_object* v_v_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_n_615_, v___x_618_, v_k_616_, v_v_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object* v_x_621_, size_t v_x_622_, size_t v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v_es_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v_j_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_es_626_ = lean_ctor_get(v_x_621_, 0);
v___x_627_ = ((size_t)31ULL);
v___x_628_ = lean_usize_land(v_x_622_, v___x_627_);
v_j_629_ = lean_usize_to_nat(v___x_628_);
v___x_630_ = lean_array_get_size(v_es_626_);
v___x_631_ = lean_nat_dec_lt(v_j_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_j_629_);
lean_dec(v_x_625_);
lean_dec_ref(v_x_624_);
return v_x_621_;
}
else
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_677_; 
lean_inc_ref(v_es_626_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v_x_621_, 0);
lean_dec(v_unused_678_);
v___x_633_ = v_x_621_;
v_isShared_634_ = v_isSharedCheck_677_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_x_621_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_677_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_v_635_; lean_object* v___x_636_; lean_object* v_xs_x27_637_; lean_object* v___y_639_; 
v_v_635_ = lean_array_fget(v_es_626_, v_j_629_);
v___x_636_ = lean_box(0);
v_xs_x27_637_ = lean_array_fset(v_es_626_, v_j_629_, v___x_636_);
switch(lean_obj_tag(v_v_635_))
{
case 0:
{
lean_object* v_key_644_; lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_662_; 
v_key_644_ = lean_ctor_get(v_v_635_, 0);
v_val_645_ = lean_ctor_get(v_v_635_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_v_635_);
if (v_isSharedCheck_662_ == 0)
{
v___x_647_ = v_v_635_;
v_isShared_648_ = v_isSharedCheck_662_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_inc(v_key_644_);
lean_dec(v_v_635_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_662_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_659_; lean_object* v_declName_661_; 
v_declName_661_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_declName_661_);
v___y_659_ = v_declName_661_;
goto v___jp_658_;
v___jp_649_:
{
uint8_t v___x_652_; 
v___x_652_ = lean_name_eq(v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_del_object(v___x_647_);
v___x_653_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_644_, v_val_645_, v_x_624_, v_x_625_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___y_639_ = v___x_654_;
goto v___jp_638_;
}
else
{
lean_object* v___x_656_; 
lean_dec(v_val_645_);
lean_dec(v_key_644_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_x_625_);
lean_ctor_set(v___x_647_, 0, v_x_624_);
v___x_656_ = v___x_647_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_x_624_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_x_625_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_639_ = v___x_656_;
goto v___jp_638_;
}
}
}
v___jp_658_:
{
lean_object* v_declName_660_; 
v_declName_660_ = lean_ctor_get(v_key_644_, 0);
lean_inc(v_declName_660_);
v___y_650_ = v___y_659_;
v___y_651_ = v_declName_660_;
goto v___jp_649_;
}
}
}
case 1:
{
lean_object* v_node_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v_node_663_ = lean_ctor_get(v_v_635_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_v_635_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v_v_635_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_node_663_);
lean_dec(v_v_635_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_667_ = ((size_t)5ULL);
v___x_668_ = lean_usize_shift_right(v_x_622_, v___x_667_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_x_623_, v___x_669_);
v___x_671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_node_663_, v___x_668_, v___x_670_, v_x_624_, v_x_625_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_671_);
v___x_673_ = v___x_665_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
v___y_639_ = v___x_673_;
goto v___jp_638_;
}
}
}
default: 
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_x_624_);
lean_ctor_set(v___x_676_, 1, v_x_625_);
v___y_639_ = v___x_676_;
goto v___jp_638_;
}
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = lean_array_fset(v_xs_x27_637_, v_j_629_, v___y_639_);
lean_dec(v_j_629_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_640_);
v___x_642_ = v___x_633_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v_ks_679_; lean_object* v_vs_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_698_; 
v_ks_679_ = lean_ctor_get(v_x_621_, 0);
v_vs_680_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_698_ == 0)
{
v___x_682_ = v_x_621_;
v_isShared_683_ = v_isSharedCheck_698_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_vs_680_);
lean_inc(v_ks_679_);
lean_dec(v_x_621_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_698_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_ks_679_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_vs_680_);
v___x_685_ = v_reuseFailAlloc_697_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v_newNode_686_; size_t v___x_687_; uint8_t v___x_688_; 
v_newNode_686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v___x_685_, v_x_624_, v_x_625_);
v___x_687_ = ((size_t)7ULL);
v___x_688_ = lean_usize_dec_le(v___x_687_, v_x_623_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_686_);
v___x_690_ = lean_unsigned_to_nat(4u);
v___x_691_ = lean_nat_dec_lt(v___x_689_, v___x_690_);
lean_dec(v___x_689_);
if (v___x_691_ == 0)
{
lean_object* v_ks_692_; lean_object* v_vs_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_ks_692_ = lean_ctor_get(v_newNode_686_, 0);
lean_inc_ref(v_ks_692_);
v_vs_693_ = lean_ctor_get(v_newNode_686_, 1);
lean_inc_ref(v_vs_693_);
lean_dec_ref(v_newNode_686_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0);
v___x_696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_x_623_, v_ks_692_, v_vs_693_, v___x_694_, v___x_695_);
lean_dec_ref(v_vs_693_);
lean_dec_ref(v_ks_692_);
return v___x_696_;
}
else
{
return v_newNode_686_;
}
}
else
{
return v_newNode_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t v_depth_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_i_702_, lean_object* v_entries_703_){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_array_get_size(v_keys_700_);
v___x_705_ = lean_nat_dec_lt(v_i_702_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec(v_i_702_);
return v_entries_703_;
}
else
{
lean_object* v_k_706_; lean_object* v_v_707_; uint64_t v___y_709_; lean_object* v___y_721_; lean_object* v_declName_724_; 
v_k_706_ = lean_array_fget_borrowed(v_keys_700_, v_i_702_);
v_v_707_ = lean_array_fget_borrowed(v_vals_701_, v_i_702_);
v_declName_724_ = lean_ctor_get(v_k_706_, 0);
lean_inc(v_declName_724_);
v___y_721_ = v_declName_724_;
goto v___jp_720_;
v___jp_708_:
{
size_t v_h_710_; size_t v___x_711_; lean_object* v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v_h_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_h_710_ = lean_uint64_to_usize(v___y_709_);
v___x_711_ = ((size_t)5ULL);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_sub(v_depth_699_, v___x_713_);
v___x_715_ = lean_usize_mul(v___x_711_, v___x_714_);
v_h_716_ = lean_usize_shift_right(v_h_710_, v___x_715_);
v___x_717_ = lean_nat_add(v_i_702_, v___x_712_);
lean_dec(v_i_702_);
lean_inc(v_v_707_);
lean_inc(v_k_706_);
v___x_718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_entries_703_, v_h_716_, v_depth_699_, v_k_706_, v_v_707_);
v_i_702_ = v___x_717_;
v_entries_703_ = v___x_718_;
goto _start;
}
v___jp_720_:
{
if (lean_obj_tag(v___y_721_) == 0)
{
uint64_t v___x_722_; 
v___x_722_ = 1723ULL;
v___y_709_ = v___x_722_;
goto v___jp_708_;
}
else
{
uint64_t v_hash_723_; 
v_hash_723_ = lean_ctor_get_uint64(v___y_721_, sizeof(void*)*2);
lean_dec(v___y_721_);
v___y_709_ = v_hash_723_;
goto v___jp_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_725_, lean_object* v_keys_726_, lean_object* v_vals_727_, lean_object* v_i_728_, lean_object* v_entries_729_){
_start:
{
size_t v_depth_boxed_730_; lean_object* v_res_731_; 
v_depth_boxed_730_ = lean_unbox_usize(v_depth_725_);
lean_dec(v_depth_725_);
v_res_731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_boxed_730_, v_keys_726_, v_vals_727_, v_i_728_, v_entries_729_);
lean_dec_ref(v_vals_727_);
lean_dec_ref(v_keys_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
size_t v_x_888__boxed_737_; size_t v_x_889__boxed_738_; lean_object* v_res_739_; 
v_x_888__boxed_737_ = lean_unbox_usize(v_x_733_);
lean_dec(v_x_733_);
v_x_889__boxed_738_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_res_739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_732_, v_x_888__boxed_737_, v_x_889__boxed_738_, v_x_735_, v_x_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
uint64_t v___y_744_; lean_object* v___y_749_; lean_object* v_declName_752_; 
v_declName_752_ = lean_ctor_get(v_x_741_, 0);
lean_inc(v_declName_752_);
v___y_749_ = v_declName_752_;
goto v___jp_748_;
v___jp_743_:
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_uint64_to_usize(v___y_744_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_740_, v___x_745_, v___x_746_, v_x_741_, v_x_742_);
return v___x_747_;
}
v___jp_748_:
{
if (lean_obj_tag(v___y_749_) == 0)
{
uint64_t v___x_750_; 
v___x_750_ = 1723ULL;
v___y_744_ = v___x_750_;
goto v___jp_743_;
}
else
{
uint64_t v_hash_751_; 
v_hash_751_ = lean_ctor_get_uint64(v___y_749_, sizeof(void*)*2);
lean_dec(v___y_749_);
v___y_744_ = v_hash_751_;
goto v___jp_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object* v_s_753_, lean_object* v_origin_754_){
_start:
{
lean_object* v_smap_755_; lean_object* v_origins_756_; lean_object* v_erased_757_; lean_object* v_omap_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
v_smap_755_ = lean_ctor_get(v_s_753_, 0);
v_origins_756_ = lean_ctor_get(v_s_753_, 1);
v_erased_757_ = lean_ctor_get(v_s_753_, 2);
v_omap_758_ = lean_ctor_get(v_s_753_, 3);
v_isSharedCheck_768_ = !lean_is_exclusive(v_s_753_);
if (v_isSharedCheck_768_ == 0)
{
v___x_760_ = v_s_753_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_omap_758_);
lean_inc(v_erased_757_);
lean_inc(v_origins_756_);
lean_inc(v_smap_755_);
lean_dec(v_s_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_762_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_origins_756_, v_origin_754_);
v___x_763_ = lean_box(0);
v___x_764_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_erased_757_, v_origin_754_, v___x_763_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_764_);
lean_ctor_set(v___x_760_, 1, v___x_762_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_smap_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_omap_758_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object* v_00_u03b1_769_, lean_object* v_s_770_, lean_object* v_origin_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_770_, v_origin_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(v_00_u03b2_777_, v_x_778_, v_x_779_);
lean_dec_ref(v_x_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_x_782_, v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_786_, lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_787_, v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
size_t v_x_1133__boxed_795_; lean_object* v_res_796_; 
v_x_1133__boxed_795_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_res_796_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(v_00_u03b2_791_, v_x_792_, v_x_1133__boxed_795_, v_x_794_);
lean_dec_ref(v_x_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, size_t v_x_799_, size_t v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_798_, v_x_799_, v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_1144__boxed_810_; size_t v_x_1145__boxed_811_; lean_object* v_res_812_; 
v_x_1144__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_x_1145__boxed_811_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(v_00_u03b2_804_, v_x_805_, v_x_1144__boxed_810_, v_x_1145__boxed_811_, v_x_808_, v_x_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_k_815_, lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v_n_814_, v_k_815_, v_v_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_818_, size_t v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_819_, v_keys_820_, v_vals_821_, v_i_823_, v_entries_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_826_, lean_object* v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_827_);
lean_dec(v_depth_827_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(v_00_u03b2_826_, v_depth_boxed_833_, v_keys_828_, v_vals_829_, v_heq_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_829_);
lean_dec_ref(v_keys_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_x_836_, v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object* v_s_841_, lean_object* v_origin_842_){
_start:
{
lean_object* v_erased_843_; uint8_t v___x_844_; 
v_erased_843_ = lean_ctor_get(v_s_841_, 2);
v___x_844_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_843_, v_origin_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object* v_s_845_, lean_object* v_origin_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_845_, v_origin_846_);
lean_dec_ref(v_origin_846_);
lean_dec_ref(v_s_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object* v_00_u03b1_849_, lean_object* v_s_850_, lean_object* v_origin_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_850_, v_origin_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object* v_00_u03b1_853_, lean_object* v_s_854_, lean_object* v_origin_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_Meta_Grind_Theorems_isErased(v_00_u03b1_853_, v_s_854_, v_origin_855_);
lean_dec_ref(v_origin_855_);
lean_dec_ref(v_s_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object* v_s_858_, lean_object* v_sym_859_){
_start:
{
lean_object* v_smap_860_; lean_object* v_origins_861_; lean_object* v_erased_862_; lean_object* v_omap_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_884_; 
v_smap_860_ = lean_ctor_get(v_s_858_, 0);
v_origins_861_ = lean_ctor_get(v_s_858_, 1);
v_erased_862_ = lean_ctor_get(v_s_858_, 2);
v_omap_863_ = lean_ctor_get(v_s_858_, 3);
v_isSharedCheck_884_ = !lean_is_exclusive(v_s_858_);
if (v_isSharedCheck_884_ == 0)
{
v___x_865_ = v_s_858_;
v_isShared_866_ = v_isSharedCheck_884_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_omap_863_);
lean_inc(v_erased_862_);
lean_inc(v_origins_861_);
lean_inc(v_smap_860_);
lean_dec(v_s_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_884_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_868_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_859_);
v___x_869_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_867_, v___x_868_, v_smap_860_, v_sym_859_);
if (lean_obj_tag(v___x_869_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_882_; 
v_val_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_882_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_882_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l_Lean_PersistentHashMap_erase___redArg(v___x_867_, v___x_868_, v_smap_860_, v_sym_859_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_874_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_origins_861_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_erased_862_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_omap_863_);
v___x_876_ = v_reuseFailAlloc_881_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_val_870_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_877_);
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
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
else
{
lean_object* v___x_883_; 
lean_dec(v___x_869_);
lean_del_object(v___x_865_);
lean_dec_ref(v_omap_863_);
lean_dec_ref(v_erased_862_);
lean_dec_ref(v_origins_861_);
lean_dec_ref(v_smap_860_);
lean_dec(v_sym_859_);
v___x_883_ = lean_box(0);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object* v_00_u03b1_885_, lean_object* v_s_886_, lean_object* v_sym_887_){
_start:
{
lean_object* v_smap_888_; lean_object* v_origins_889_; lean_object* v_erased_890_; lean_object* v_omap_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_912_; 
v_smap_888_ = lean_ctor_get(v_s_886_, 0);
v_origins_889_ = lean_ctor_get(v_s_886_, 1);
v_erased_890_ = lean_ctor_get(v_s_886_, 2);
v_omap_891_ = lean_ctor_get(v_s_886_, 3);
v_isSharedCheck_912_ = !lean_is_exclusive(v_s_886_);
if (v_isSharedCheck_912_ == 0)
{
v___x_893_ = v_s_886_;
v_isShared_894_ = v_isSharedCheck_912_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_omap_891_);
lean_inc(v_erased_890_);
lean_inc(v_origins_889_);
lean_inc(v_smap_888_);
lean_dec(v_s_886_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_912_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_896_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_887_);
v___x_897_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_895_, v___x_896_, v_smap_888_, v_sym_887_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
v_val_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_910_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = l_Lean_PersistentHashMap_erase___redArg(v___x_895_, v___x_896_, v_smap_888_, v_sym_887_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_902_);
v___x_904_ = v___x_893_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_origins_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_erased_890_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_omap_891_);
v___x_904_ = v_reuseFailAlloc_909_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_val_898_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_905_);
v___x_907_ = v___x_900_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v___x_897_);
lean_del_object(v___x_893_);
lean_dec_ref(v_omap_891_);
lean_dec_ref(v_erased_890_);
lean_dec_ref(v_origins_889_);
lean_dec_ref(v_smap_888_);
lean_dec(v_sym_887_);
v___x_911_ = lean_box(0);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_913_, lean_object* v_vals_914_, lean_object* v_i_915_, lean_object* v_k_916_){
_start:
{
lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_array_get_size(v_keys_913_);
v___x_927_ = lean_nat_dec_lt(v_i_915_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec(v_i_915_);
v___x_928_ = lean_box(0);
return v___x_928_;
}
else
{
lean_object* v_k_x27_929_; lean_object* v___y_931_; lean_object* v_declName_933_; 
v_k_x27_929_ = lean_array_fget_borrowed(v_keys_913_, v_i_915_);
v_declName_933_ = lean_ctor_get(v_k_916_, 0);
v___y_931_ = v_declName_933_;
goto v___jp_930_;
v___jp_930_:
{
lean_object* v_declName_932_; 
v_declName_932_ = lean_ctor_get(v_k_x27_929_, 0);
v___y_918_ = v___y_931_;
v___y_919_ = v_declName_932_;
goto v___jp_917_;
}
}
v___jp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = lean_name_eq(v___y_918_, v___y_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_i_915_, v___x_921_);
lean_dec(v_i_915_);
v_i_915_ = v___x_922_;
goto _start;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_array_fget_borrowed(v_vals_914_, v_i_915_);
lean_dec(v_i_915_);
lean_inc(v___x_924_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_i_936_, lean_object* v_k_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_934_, v_vals_935_, v_i_936_, v_k_937_);
lean_dec_ref(v_k_937_);
lean_dec_ref(v_vals_935_);
lean_dec_ref(v_keys_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object* v_x_939_, size_t v_x_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v_es_942_; lean_object* v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v_j_946_; lean_object* v___x_947_; 
v_es_942_ = lean_ctor_get(v_x_939_, 0);
v___x_943_ = lean_box(2);
v___x_944_ = ((size_t)31ULL);
v___x_945_ = lean_usize_land(v_x_940_, v___x_944_);
v_j_946_ = lean_usize_to_nat(v___x_945_);
v___x_947_ = lean_array_get_borrowed(v___x_943_, v_es_942_, v_j_946_);
lean_dec(v_j_946_);
switch(lean_obj_tag(v___x_947_))
{
case 0:
{
lean_object* v_key_948_; lean_object* v_val_949_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_957_; lean_object* v_declName_959_; 
v_key_948_ = lean_ctor_get(v___x_947_, 0);
v_val_949_ = lean_ctor_get(v___x_947_, 1);
v_declName_959_ = lean_ctor_get(v_x_941_, 0);
v___y_957_ = v_declName_959_;
goto v___jp_956_;
v___jp_950_:
{
uint8_t v___x_953_; 
v___x_953_ = lean_name_eq(v___y_951_, v___y_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
v___x_954_ = lean_box(0);
return v___x_954_;
}
else
{
lean_object* v___x_955_; 
lean_inc(v_val_949_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v_val_949_);
return v___x_955_;
}
}
v___jp_956_:
{
lean_object* v_declName_958_; 
v_declName_958_ = lean_ctor_get(v_key_948_, 0);
v___y_951_ = v___y_957_;
v___y_952_ = v_declName_958_;
goto v___jp_950_;
}
}
case 1:
{
lean_object* v_node_960_; size_t v___x_961_; size_t v___x_962_; 
v_node_960_ = lean_ctor_get(v___x_947_, 0);
v___x_961_ = ((size_t)5ULL);
v___x_962_ = lean_usize_shift_right(v_x_940_, v___x_961_);
v_x_939_ = v_node_960_;
v_x_940_ = v___x_962_;
goto _start;
}
default: 
{
lean_object* v___x_964_; 
v___x_964_ = lean_box(0);
return v___x_964_;
}
}
}
else
{
lean_object* v_ks_965_; lean_object* v_vs_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_ks_965_ = lean_ctor_get(v_x_939_, 0);
v_vs_966_ = lean_ctor_get(v_x_939_, 1);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_ks_965_, v_vs_966_, v___x_967_, v_x_941_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
size_t v_x_225__boxed_972_; lean_object* v_res_973_; 
v_x_225__boxed_972_ = lean_unbox_usize(v_x_970_);
lean_dec(v_x_970_);
v_res_973_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_969_, v_x_225__boxed_972_, v_x_971_);
lean_dec_ref(v_x_971_);
lean_dec_ref(v_x_969_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
uint64_t v___y_977_; lean_object* v___y_981_; lean_object* v_declName_984_; 
v_declName_984_ = lean_ctor_get(v_x_975_, 0);
v___y_981_ = v_declName_984_;
goto v___jp_980_;
v___jp_976_:
{
size_t v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_uint64_to_usize(v___y_977_);
v___x_979_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_974_, v___x_978_, v_x_975_);
return v___x_979_;
}
v___jp_980_:
{
if (lean_obj_tag(v___y_981_) == 0)
{
uint64_t v___x_982_; 
v___x_982_ = 1723ULL;
v___y_977_ = v___x_982_;
goto v___jp_976_;
}
else
{
uint64_t v_hash_983_; 
v_hash_983_ = lean_ctor_get_uint64(v___y_981_, sizeof(void*)*2);
v___y_977_ = v_hash_983_;
goto v___jp_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_985_, v_x_986_);
lean_dec_ref(v_x_986_);
lean_dec_ref(v_x_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object* v_s_988_, lean_object* v_origin_989_){
_start:
{
lean_object* v_omap_990_; lean_object* v___x_991_; 
v_omap_990_ = lean_ctor_get(v_s_988_, 3);
v___x_991_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_omap_990_, v_origin_989_);
if (lean_obj_tag(v___x_991_) == 1)
{
lean_object* v_val_992_; 
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
return v_val_992_;
}
else
{
lean_object* v___x_993_; 
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object* v_s_994_, lean_object* v_origin_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_994_, v_origin_995_);
lean_dec_ref(v_origin_995_);
lean_dec_ref(v_s_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object* v_00_u03b1_997_, lean_object* v_s_998_, lean_object* v_origin_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_998_, v_origin_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_s_1002_, lean_object* v_origin_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_Grind_Theorems_find(v_00_u03b1_1001_, v_s_1002_, v_origin_1003_);
lean_dec_ref(v_origin_1003_);
lean_dec_ref(v_s_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_1006_, v_x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(v_00_u03b2_1009_, v_x_1010_, v_x_1011_);
lean_dec_ref(v_x_1011_);
lean_dec_ref(v_x_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, size_t v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_1014_, v_x_1015_, v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
size_t v_x_336__boxed_1022_; lean_object* v_res_1023_; 
v_x_336__boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_res_1023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(v_00_u03b2_1018_, v_x_1019_, v_x_336__boxed_1022_, v_x_1021_);
lean_dec_ref(v_x_1021_);
lean_dec_ref(v_x_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1024_, lean_object* v_keys_1025_, lean_object* v_vals_1026_, lean_object* v_heq_1027_, lean_object* v_i_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_1025_, v_vals_1026_, v_i_1028_, v_k_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(v_00_u03b2_1031_, v_keys_1032_, v_vals_1033_, v_heq_1034_, v_i_1035_, v_k_1036_);
lean_dec_ref(v_k_1036_);
lean_dec_ref(v_vals_1033_);
lean_dec_ref(v_keys_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(v_x_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v_x_1045_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0(void){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_instMonadEIO___redArg();
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0);
v___x_1054_ = l_StateRefT_x27_instMonad___redArg(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___f_1060_; 
v___x_1059_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1060_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1060_, 0, v___x_1059_);
return v___f_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___f_1062_; 
v___x_1061_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1062_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1062_, 0, v___x_1061_);
return v___f_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8(void){
_start:
{
lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; 
v___f_1063_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7);
v___f_1064_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___f_1064_);
lean_ctor_set(v___x_1065_, 1, v___f_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___f_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1067_, 0, v___x_1066_);
return v___f_1067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1069_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
return v___f_1069_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11(void){
_start:
{
lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; 
v___f_1070_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10);
v___f_1071_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___f_1071_);
lean_ctor_set(v___x_1072_, 1, v___f_1070_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15));
v___x_1079_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14));
v___x_1080_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1079_, v___x_1078_, v___x_1077_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16);
v___f_1082_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13));
v___f_1083_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12));
v___x_1084_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1083_, v___f_1082_, v___x_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object* v_inst_1086_, lean_object* v_thm_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_toApplicative_1094_; lean_object* v_toFunctor_1095_; lean_object* v_toSeq_1096_; lean_object* v_toSeqLeft_1097_; lean_object* v_toSeqRight_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_toApplicative_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1201_; 
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1);
v_toApplicative_1094_ = lean_ctor_get(v___x_1093_, 0);
v_toFunctor_1095_ = lean_ctor_get(v_toApplicative_1094_, 0);
v_toSeq_1096_ = lean_ctor_get(v_toApplicative_1094_, 2);
v_toSeqLeft_1097_ = lean_ctor_get(v_toApplicative_1094_, 3);
v_toSeqRight_1098_ = lean_ctor_get(v_toApplicative_1094_, 4);
v___f_1099_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2));
v___f_1100_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1095_, 2);
v___f_1101_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1101_, 0, v_toFunctor_1095_);
v___f_1102_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1102_, 0, v_toFunctor_1095_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___f_1101_);
lean_ctor_set(v___x_1103_, 1, v___f_1102_);
lean_inc(v_toSeqRight_1098_);
v___f_1104_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1104_, 0, v_toSeqRight_1098_);
lean_inc(v_toSeqLeft_1097_);
v___f_1105_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1105_, 0, v_toSeqLeft_1097_);
lean_inc(v_toSeq_1096_);
v___f_1106_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1106_, 0, v_toSeq_1096_);
v___x_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1103_);
lean_ctor_set(v___x_1107_, 1, v___f_1099_);
lean_ctor_set(v___x_1107_, 2, v___f_1106_);
lean_ctor_set(v___x_1107_, 3, v___f_1105_);
lean_ctor_set(v___x_1107_, 4, v___f_1104_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___f_1100_);
v___x_1109_ = l_StateRefT_x27_instMonad___redArg(v___x_1108_);
v_toApplicative_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1109_, 1);
lean_dec(v_unused_1202_);
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1201_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_toApplicative_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1201_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_toFunctor_1114_; lean_object* v_toSeq_1115_; lean_object* v_toSeqLeft_1116_; lean_object* v_toSeqRight_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1199_; 
v_toFunctor_1114_ = lean_ctor_get(v_toApplicative_1110_, 0);
v_toSeq_1115_ = lean_ctor_get(v_toApplicative_1110_, 2);
v_toSeqLeft_1116_ = lean_ctor_get(v_toApplicative_1110_, 3);
v_toSeqRight_1117_ = lean_ctor_get(v_toApplicative_1110_, 4);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_toApplicative_1110_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_toApplicative_1110_, 1);
lean_dec(v_unused_1200_);
v___x_1119_ = v_toApplicative_1110_;
v_isShared_1120_ = v_isSharedCheck_1199_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_toSeqRight_1117_);
lean_inc(v_toSeqLeft_1116_);
lean_inc(v_toSeq_1115_);
lean_inc(v_toFunctor_1114_);
lean_dec(v_toApplicative_1110_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1199_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___x_1130_; 
v___f_1121_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
v___f_1122_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
lean_inc_ref(v_toFunctor_1114_);
v___f_1123_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1123_, 0, v_toFunctor_1114_);
v___f_1124_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1124_, 0, v_toFunctor_1114_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___f_1123_);
lean_ctor_set(v___x_1125_, 1, v___f_1124_);
v___f_1126_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1126_, 0, v_toSeqRight_1117_);
v___f_1127_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1127_, 0, v_toSeqLeft_1116_);
v___f_1128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1128_, 0, v_toSeq_1115_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 4, v___f_1126_);
lean_ctor_set(v___x_1119_, 3, v___f_1127_);
lean_ctor_set(v___x_1119_, 2, v___f_1128_);
lean_ctor_set(v___x_1119_, 1, v___f_1121_);
lean_ctor_set(v___x_1119_, 0, v___x_1125_);
v___x_1130_ = v___x_1119_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___f_1121_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___f_1128_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v___f_1127_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___f_1126_);
v___x_1130_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___f_1122_);
lean_ctor_set(v___x_1112_, 0, v___x_1130_);
v___x_1132_ = v___x_1112_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___f_1122_);
v___x_1132_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_toMonadRef_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_getProof_1140_; lean_object* v_getLevelParams_1141_; lean_object* v___f_1142_; lean_object* v_proof_1143_; lean_object* v_us_1144_; uint8_t v___x_1171_; 
v___x_1133_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11);
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17);
v_toMonadRef_1136_ = lean_ctor_get(v___x_1135_, 0);
v___x_1137_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_1132_);
v___x_1138_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1137_, v___x_1132_);
lean_inc_ref(v_toMonadRef_1136_);
v___x_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1134_);
lean_ctor_set(v___x_1139_, 1, v_toMonadRef_1136_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
v_getProof_1140_ = lean_ctor_get(v_inst_1086_, 3);
lean_inc_ref(v_getProof_1140_);
v_getLevelParams_1141_ = lean_ctor_get(v_inst_1086_, 4);
lean_inc_ref(v_getLevelParams_1141_);
lean_dec_ref(v_inst_1086_);
v___f_1142_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18));
lean_inc(v_thm_1087_);
v_proof_1143_ = lean_apply_1(v_getProof_1140_, v_thm_1087_);
v_us_1144_ = lean_apply_1(v_getLevelParams_1141_, v_thm_1087_);
v___x_1171_ = l_Lean_Expr_isConst(v_proof_1143_);
if (v___x_1171_ == 0)
{
lean_dec_ref_known(v___x_1139_, 3);
goto v___jp_1145_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_array_get_size(v_us_1144_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_nat_dec_eq(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec_ref_known(v___x_1139_, 3);
goto v___jp_1145_;
}
else
{
lean_object* v_declName_1175_; lean_object* v___x_742__overap_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_us_1144_);
v_declName_1175_ = l_Lean_Expr_constName_x21(v_proof_1143_);
lean_inc(v_declName_1175_);
v___x_742__overap_1176_ = l_Lean_getConstVal___redArg(v___x_1132_, v___x_1133_, v___x_1139_, v_declName_1175_);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
v___x_1177_ = lean_apply_5(v___x_742__overap_1176_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, lean_box(0));
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1188_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_levelParams_1182_; uint8_t v___x_1183_; 
v_levelParams_1182_ = lean_ctor_get(v_a_1178_, 1);
lean_inc(v_levelParams_1182_);
lean_dec(v_a_1178_);
v___x_1183_ = l_List_isEmpty___redArg(v_levelParams_1182_);
lean_dec(v_levelParams_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_del_object(v___x_1180_);
lean_dec_ref(v_proof_1143_);
v___x_1184_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_1175_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v___x_1184_;
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_declName_1175_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_proof_1143_);
v___x_1186_ = v___x_1180_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_proof_1143_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_declName_1175_);
lean_dec_ref(v_proof_1143_);
v_a_1189_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1177_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
v___jp_1145_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_array_get_size(v_us_1144_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_nat_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
size_t v_sz_1149_; size_t v___x_1150_; lean_object* v___x_695__overap_1151_; lean_object* v___x_1152_; 
v_sz_1149_ = lean_array_size(v_us_1144_);
v___x_1150_ = ((size_t)0ULL);
lean_inc_ref(v_us_1144_);
v___x_695__overap_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1142_, v_sz_1149_, v___x_1150_, v_us_1144_);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
v___x_1152_ = lean_apply_5(v___x_695__overap_1151_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, lean_box(0));
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = l_Lean_Expr_instantiateLevelParamsArray(v_proof_1143_, v_us_1144_, v_a_1153_);
lean_dec_ref(v_proof_1143_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_us_1144_);
lean_dec_ref(v_proof_1143_);
v_a_1162_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1152_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1152_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v___x_1170_; 
lean_dec_ref(v_us_1144_);
lean_dec_ref(v___x_1132_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_proof_1143_);
return v___x_1170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object* v_inst_1203_, lean_object* v_thm_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1203_, v_thm_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object* v_00_u03b1_1211_, lean_object* v_inst_1212_, lean_object* v_thm_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1212_, v_thm_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_inst_1221_, lean_object* v_thm_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(v_00_u03b1_1220_, v_inst_1221_, v_thm_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_env_1236_; uint8_t v___x_1237_; lean_object* v_env_1238_; lean_object* v___x_1239_; lean_object* v_toCold_1240_; lean_object* v_mctx_1241_; lean_object* v_lctx_1242_; lean_object* v_options_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1235_ = lean_st_ref_get(v___y_1233_);
v_env_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc_ref(v_env_1236_);
lean_dec(v___x_1235_);
v___x_1237_ = 0;
v_env_1238_ = l_Lean_Environment_setRecordingDeps(v_env_1236_, v___x_1237_);
v___x_1239_ = lean_st_ref_get(v___y_1231_);
v_toCold_1240_ = lean_ctor_get(v___y_1232_, 0);
v_mctx_1241_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_mctx_1241_);
lean_dec(v___x_1239_);
v_lctx_1242_ = lean_ctor_get(v___y_1230_, 2);
v_options_1243_ = lean_ctor_get(v_toCold_1240_, 2);
lean_inc_ref(v_options_1243_);
lean_inc_ref(v_lctx_1242_);
v___x_1244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1244_, 0, v_env_1238_);
lean_ctor_set(v___x_1244_, 1, v_mctx_1241_);
lean_ctor_set(v___x_1244_, 2, v_lctx_1242_);
lean_ctor_set(v___x_1244_, 3, v_options_1243_);
v___x_1245_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_msgData_1229_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_msgData_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object* v_msg_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_ref_1260_; lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_ref_1260_ = lean_ctor_get(v___y_1257_, 2);
v___x_1261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msg_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_inc(v_ref_1260_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_ref_1260_);
lean_ctor_set(v___x_1266_, 1, v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object* v_declName_1284_, lean_object* v_00_u03b1_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1292_ = 0;
v___x_1293_ = l_Lean_MessageData_ofConstName(v_declName_1284_, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_1296_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object* v_declName_1298_, lean_object* v_00_u03b1_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1298_, v_00_u03b1_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object* v_s_1306_, uint8_t v___x_1307_, lean_object* v_as_1308_, size_t v_i_1309_, size_t v_stop_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_usize_dec_eq(v_i_1309_, v_stop_1310_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1312_ = 1;
v___x_1313_ = lean_array_uget_borrowed(v_as_1308_, v_i_1309_);
lean_inc(v___x_1313_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
v___x_1315_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1306_, v___x_1314_);
lean_dec_ref_known(v___x_1314_, 1);
if (v___x_1315_ == 0)
{
return v___x_1312_;
}
else
{
if (v___x_1307_ == 0)
{
size_t v___x_1316_; size_t v___x_1317_; 
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1309_, v___x_1316_);
v_i_1309_ = v___x_1317_;
goto _start;
}
else
{
return v___x_1312_;
}
}
}
else
{
uint8_t v___x_1319_; 
v___x_1319_ = 0;
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object* v_s_1320_, lean_object* v___x_1321_, lean_object* v_as_1322_, lean_object* v_i_1323_, lean_object* v_stop_1324_){
_start:
{
uint8_t v___x_2904__boxed_1325_; size_t v_i_boxed_1326_; size_t v_stop_boxed_1327_; uint8_t v_res_1328_; lean_object* v_r_1329_; 
v___x_2904__boxed_1325_ = lean_unbox(v___x_1321_);
v_i_boxed_1326_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_stop_boxed_1327_ = lean_unbox_usize(v_stop_1324_);
lean_dec(v_stop_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1320_, v___x_2904__boxed_1325_, v_as_1322_, v_i_boxed_1326_, v_stop_boxed_1327_);
lean_dec_ref(v_as_1322_);
lean_dec_ref(v_s_1320_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object* v_as_1330_, size_t v_i_1331_, size_t v_stop_1332_, lean_object* v_b_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_eq(v_i_1331_, v_stop_1332_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; 
v___x_1335_ = lean_array_uget_borrowed(v_as_1330_, v_i_1331_);
lean_inc(v___x_1335_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
v___x_1337_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_b_1333_, v___x_1336_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1331_, v___x_1338_);
v_i_1331_ = v___x_1339_;
v_b_1333_ = v___x_1337_;
goto _start;
}
else
{
return v_b_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_as_1341_, lean_object* v_i_1342_, lean_object* v_stop_1343_, lean_object* v_b_1344_){
_start:
{
size_t v_i_boxed_1345_; size_t v_stop_boxed_1346_; lean_object* v_res_1347_; 
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_stop_boxed_1346_ = lean_unbox_usize(v_stop_1343_);
lean_dec(v_stop_1343_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1341_, v_i_boxed_1345_, v_stop_boxed_1346_, v_b_1344_);
lean_dec_ref(v_as_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object* v_s_1348_, lean_object* v_declName_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1359_; lean_object* v_env_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_st_ref_get(v_a_1353_);
v_env_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_ref(v_env_1360_);
lean_dec(v___x_1359_);
lean_inc(v_declName_1349_);
v___x_1361_ = l_Lean_wasOriginallyTheorem(v_env_1360_, v_declName_1349_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_inc(v_declName_1349_);
v___x_1362_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1397_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1397_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1397_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
if (lean_obj_tag(v_a_1363_) == 1)
{
lean_object* v_val_1367_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_val_1367_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v_a_1363_, 1);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_array_get_size(v_val_1367_);
v___x_1383_ = lean_nat_dec_lt(v___x_1381_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec(v_declName_1349_);
goto v___jp_1368_;
}
else
{
if (v___x_1383_ == 0)
{
lean_dec(v_declName_1349_);
goto v___jp_1368_;
}
else
{
size_t v___x_1384_; size_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = lean_usize_of_nat(v___x_1382_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1348_, v___x_1361_, v_val_1367_, v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v_declName_1349_);
goto v___jp_1368_;
}
else
{
lean_object* v___x_1387_; lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_val_1367_);
lean_del_object(v___x_1365_);
lean_dec_ref(v_s_1348_);
v___x_1387_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1349_, lean_box(0), v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
v___jp_1368_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_val_1367_);
v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1373_; 
lean_dec(v_val_1367_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v_s_1348_);
v___x_1373_ = v___x_1365_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_s_1348_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1370_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1367_, v___x_1375_, v___x_1376_, v_s_1348_);
lean_dec(v_val_1367_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1377_);
v___x_1379_ = v___x_1365_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v___x_1396_; 
lean_del_object(v___x_1365_);
lean_dec(v_a_1363_);
lean_dec_ref(v_s_1348_);
v___x_1396_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1349_, lean_box(0), v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_declName_1349_);
lean_dec_ref(v_s_1348_);
v_a_1398_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1362_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1362_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v___x_1406_; uint8_t v___x_1407_; 
lean_inc(v_declName_1349_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_declName_1349_);
v___x_1407_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1348_, v___x_1406_);
lean_dec_ref_known(v___x_1406_, 1);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_s_1348_);
v___x_1408_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1349_, lean_box(0), v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
goto v___jp_1355_;
}
}
v___jp_1355_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_declName_1349_);
v___x_1357_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_1348_, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object* v_s_1417_, lean_object* v_declName_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1417_, v_declName_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object* v_00_u03b1_1425_, lean_object* v_s_1426_, lean_object* v_declName_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1426_, v_declName_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_s_1435_, lean_object* v_declName_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Meta_Grind_Theorems_eraseDecl(v_00_u03b1_1434_, v_s_1435_, v_declName_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object* v_00_u03b1_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(v_00_u03b1_1451_, v_msg_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object* v_00_u03b1_1459_, lean_object* v_as_1460_, size_t v_i_1461_, size_t v_stop_1462_, lean_object* v_b_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1460_, v_i_1461_, v_stop_1462_, v_b_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_as_1466_, lean_object* v_i_1467_, lean_object* v_stop_1468_, lean_object* v_b_1469_){
_start:
{
size_t v_i_boxed_1470_; size_t v_stop_boxed_1471_; lean_object* v_res_1472_; 
v_i_boxed_1470_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_stop_boxed_1471_ = lean_unbox_usize(v_stop_1468_);
lean_dec(v_stop_1468_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(v_00_u03b1_1465_, v_as_1466_, v_i_boxed_1470_, v_stop_boxed_1471_, v_b_1469_);
lean_dec_ref(v_as_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object* v_00_u03b1_1473_, lean_object* v_s_1474_, uint8_t v___x_1475_, lean_object* v_as_1476_, size_t v_i_1477_, size_t v_stop_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1474_, v___x_1475_, v_as_1476_, v_i_1477_, v_stop_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_s_1481_, lean_object* v___x_1482_, lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_){
_start:
{
uint8_t v___x_3090__boxed_1486_; size_t v_i_boxed_1487_; size_t v_stop_boxed_1488_; uint8_t v_res_1489_; lean_object* v_r_1490_; 
v___x_3090__boxed_1486_ = lean_unbox(v___x_1482_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1488_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(v_00_u03b1_1480_, v_s_1481_, v___x_3090__boxed_1486_, v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_);
lean_dec_ref(v_as_1483_);
lean_dec_ref(v_s_1481_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
if (lean_obj_tag(v_a_1491_) == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = l_List_reverse___redArg(v_a_1492_);
return v___x_1493_;
}
else
{
lean_object* v_head_1494_; lean_object* v_tail_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1504_; 
v_head_1494_ = lean_ctor_get(v_a_1491_, 0);
v_tail_1495_ = lean_ctor_get(v_a_1491_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_a_1491_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1497_ = v_a_1491_;
v_isShared_1498_ = v_isSharedCheck_1504_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_tail_1495_);
lean_inc(v_head_1494_);
lean_dec(v_a_1491_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1504_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_fst_1499_; lean_object* v___x_1501_; 
v_fst_1499_ = lean_ctor_get(v_head_1494_, 0);
lean_inc(v_fst_1499_);
lean_dec(v_head_1494_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_a_1492_);
lean_ctor_set(v___x_1497_, 0, v_fst_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_fst_1499_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_a_1492_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
v_a_1491_ = v_tail_1495_;
v_a_1492_ = v___x_1501_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_1505_, lean_object* v_k_1506_, lean_object* v_v_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_k_1506_);
lean_ctor_set(v___x_1508_, 1, v_v_1507_);
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v_ps_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1510_, lean_object* v_x1_1511_, lean_object* v_x2_1512_, lean_object* v_x3_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_apply_3(v_f_1510_, v_x1_1511_, v_x2_1512_, v_x3_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_f_1515_, lean_object* v_keys_1516_, lean_object* v_vals_1517_, lean_object* v_i_1518_, lean_object* v_acc_1519_){
_start:
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = lean_array_get_size(v_keys_1516_);
v___x_1521_ = lean_nat_dec_lt(v_i_1518_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec(v_i_1518_);
lean_dec(v_f_1515_);
return v_acc_1519_;
}
else
{
lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_k_1522_ = lean_array_fget_borrowed(v_keys_1516_, v_i_1518_);
v_v_1523_ = lean_array_fget_borrowed(v_vals_1517_, v_i_1518_);
lean_inc(v_f_1515_);
lean_inc(v_v_1523_);
lean_inc(v_k_1522_);
v___x_1524_ = lean_apply_3(v_f_1515_, v_acc_1519_, v_k_1522_, v_v_1523_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_i_1518_, v___x_1525_);
lean_dec(v_i_1518_);
v_i_1518_ = v___x_1526_;
v_acc_1519_ = v___x_1524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_f_1528_, lean_object* v_keys_1529_, lean_object* v_vals_1530_, lean_object* v_i_1531_, lean_object* v_acc_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1528_, v_keys_1529_, v_vals_1530_, v_i_1531_, v_acc_1532_);
lean_dec_ref(v_vals_1530_);
lean_dec_ref(v_keys_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_f_1534_, lean_object* v_as_1535_, size_t v_i_1536_, size_t v_stop_1537_, lean_object* v_b_1538_){
_start:
{
lean_object* v___y_1540_; uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_eq(v_i_1536_, v_stop_1537_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_array_uget_borrowed(v_as_1535_, v_i_1536_);
switch(lean_obj_tag(v___x_1545_))
{
case 0:
{
lean_object* v_key_1546_; lean_object* v_val_1547_; lean_object* v___x_1548_; 
v_key_1546_ = lean_ctor_get(v___x_1545_, 0);
v_val_1547_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_f_1534_);
lean_inc(v_val_1547_);
lean_inc(v_key_1546_);
v___x_1548_ = lean_apply_3(v_f_1534_, v_b_1538_, v_key_1546_, v_val_1547_);
v___y_1540_ = v___x_1548_;
goto v___jp_1539_;
}
case 1:
{
lean_object* v_node_1549_; lean_object* v___x_1550_; 
v_node_1549_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_f_1534_);
v___x_1550_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1534_, v_node_1549_, v_b_1538_);
v___y_1540_ = v___x_1550_;
goto v___jp_1539_;
}
default: 
{
v___y_1540_ = v_b_1538_;
goto v___jp_1539_;
}
}
}
else
{
lean_dec(v_f_1534_);
return v_b_1538_;
}
v___jp_1539_:
{
size_t v___x_1541_; size_t v___x_1542_; 
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1536_, v___x_1541_);
v_i_1536_ = v___x_1542_;
v_b_1538_ = v___y_1540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_f_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v_es_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_es_1554_ = lean_ctor_get(v_x_1552_, 0);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_es_1554_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v_f_1551_);
return v_x_1553_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = lean_usize_of_nat(v___x_1556_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1551_, v_es_1554_, v___x_1558_, v___x_1559_, v_x_1553_);
return v___x_1560_;
}
}
else
{
lean_object* v_ks_1561_; lean_object* v_vs_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_ks_1561_ = lean_ctor_get(v_x_1552_, 0);
v_vs_1562_ = lean_ctor_get(v_x_1552_, 1);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1551_, v_ks_1561_, v_vs_1562_, v___x_1563_, v_x_1553_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1565_, v_x_1566_, v_x_1567_);
lean_dec_ref(v_x_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_f_1569_, lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_stop_1572_, lean_object* v_b_1573_){
_start:
{
size_t v_i_boxed_1574_; size_t v_stop_boxed_1575_; lean_object* v_res_1576_; 
v_i_boxed_1574_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_stop_boxed_1575_ = lean_unbox_usize(v_stop_1572_);
lean_dec(v_stop_1572_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1569_, v_as_1570_, v_i_boxed_1574_, v_stop_boxed_1575_, v_b_1573_);
lean_dec_ref(v_as_1570_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1577_, lean_object* v_f_1578_, lean_object* v_init_1579_){
_start:
{
lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1580_, 0, v_f_1578_);
v___x_1581_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v___f_1580_, v_map_1577_, v_init_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1582_, lean_object* v_f_1583_, lean_object* v_init_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1582_, v_f_1583_, v_init_1584_);
lean_dec_ref(v_map_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object* v_m_1587_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___f_1588_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0));
v___x_1589_ = lean_box(0);
v___x_1590_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_m_1587_, v___f_1588_, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object* v_m_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1591_);
lean_dec_ref(v_m_1591_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object* v_s_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_s_1593_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(v___x_1594_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object* v_s_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_s_1597_);
lean_dec_ref(v_s_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object* v_s_1599_){
_start:
{
lean_object* v_origins_1600_; lean_object* v___x_1601_; 
v_origins_1600_ = lean_ctor_get(v_s_1599_, 1);
v___x_1601_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_origins_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object* v_s_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1602_);
lean_dec_ref(v_s_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object* v_00_u03b1_1604_, lean_object* v_s_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_s_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_Grind_Theorems_getOrigins(v_00_u03b1_1607_, v_s_1608_);
lean_dec_ref(v_s_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object* v_00_u03b2_1610_, lean_object* v_m_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(v_00_u03b2_1613_, v_m_1614_);
lean_dec_ref(v_m_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_map_1618_, lean_object* v_f_1619_, lean_object* v_init_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1618_, v_f_1619_, v_init_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1622_, lean_object* v_00_u03b2_1623_, lean_object* v_map_1624_, lean_object* v_f_1625_, lean_object* v_init_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(v_00_u03c3_1622_, v_00_u03b2_1623_, v_map_1624_, v_f_1625_, v_init_1626_);
lean_dec_ref(v_map_1624_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1628_, lean_object* v_f_1629_, lean_object* v_init_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1629_, v_map_1628_, v_init_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1632_, lean_object* v_f_1633_, lean_object* v_init_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(v_map_1632_, v_f_1633_, v_init_1634_);
lean_dec_ref(v_map_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_map_1638_, lean_object* v_f_1639_, lean_object* v_init_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1639_, v_map_1638_, v_init_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_map_1644_, lean_object* v_f_1645_, lean_object* v_init_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(v_00_u03c3_1642_, v_00_u03b2_1643_, v_map_1644_, v_f_1645_, v_init_1646_);
lean_dec_ref(v_map_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1648_, lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_f_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1651_, v_x_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1655_, lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_f_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03c3_1655_, v_00_u03b1_1656_, v_00_u03b2_1657_, v_f_1658_, v_x_1659_, v_x_1660_);
lean_dec_ref(v_x_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_00_u03c3_1664_, lean_object* v_f_1665_, lean_object* v_as_1666_, size_t v_i_1667_, size_t v_stop_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1665_, v_as_1666_, v_i_1667_, v_stop_1668_, v_b_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_00_u03c3_1673_, lean_object* v_f_1674_, lean_object* v_as_1675_, lean_object* v_i_1676_, lean_object* v_stop_1677_, lean_object* v_b_1678_){
_start:
{
size_t v_i_boxed_1679_; size_t v_stop_boxed_1680_; lean_object* v_res_1681_; 
v_i_boxed_1679_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_stop_boxed_1680_ = lean_unbox_usize(v_stop_1677_);
lean_dec(v_stop_1677_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_00_u03b1_1671_, v_00_u03b2_1672_, v_00_u03c3_1673_, v_f_1674_, v_as_1675_, v_i_boxed_1679_, v_stop_boxed_1680_, v_b_1678_);
lean_dec_ref(v_as_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03c3_1682_, lean_object* v_00_u03b1_1683_, lean_object* v_00_u03b2_1684_, lean_object* v_f_1685_, lean_object* v_keys_1686_, lean_object* v_vals_1687_, lean_object* v_heq_1688_, lean_object* v_i_1689_, lean_object* v_acc_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1685_, v_keys_1686_, v_vals_1687_, v_i_1689_, v_acc_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03c3_1692_, lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_f_1695_, lean_object* v_keys_1696_, lean_object* v_vals_1697_, lean_object* v_heq_1698_, lean_object* v_i_1699_, lean_object* v_acc_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03c3_1692_, v_00_u03b1_1693_, v_00_u03b2_1694_, v_f_1695_, v_keys_1696_, v_vals_1697_, v_heq_1698_, v_i_1699_, v_acc_1700_);
lean_dec_ref(v_vals_1697_);
lean_dec_ref(v_keys_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg(){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg___boxed(lean_object* v___dummy_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object* v_00_u03b1_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg(){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg___boxed(lean_object* v___dummy_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg();
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object* v_00_u03b1_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
if (lean_obj_tag(v_a_1715_) == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = l_List_reverse___redArg(v_a_1716_);
return v___x_1717_;
}
else
{
lean_object* v_head_1718_; lean_object* v_tail_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1728_; 
v_head_1718_ = lean_ctor_get(v_a_1715_, 0);
v_tail_1719_ = lean_ctor_get(v_a_1715_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1715_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1721_ = v_a_1715_;
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_tail_1719_);
lean_inc(v_head_1718_);
lean_dec(v_a_1715_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = l_Lean_mkLevelParam(v_head_1718_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_a_1716_);
lean_ctor_set(v___x_1721_, 0, v___x_1723_);
v___x_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_a_1716_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v_a_1715_ = v_tail_1719_;
v_a_1716_ = v___x_1725_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1731_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
lean_ctor_set(v___x_1734_, 2, v___x_1733_);
lean_ctor_set(v___x_1734_, 3, v___x_1733_);
lean_ctor_set(v___x_1734_, 4, v___x_1732_);
lean_ctor_set(v___x_1734_, 5, v___x_1732_);
lean_ctor_set(v___x_1734_, 6, v___x_1732_);
lean_ctor_set(v___x_1734_, 7, v___x_1732_);
lean_ctor_set(v___x_1734_, 8, v___x_1732_);
lean_ctor_set(v___x_1734_, 9, v___x_1732_);
lean_ctor_set(v___x_1734_, 10, v___x_1732_);
lean_ctor_set(v___x_1734_, 11, v___x_1731_);
return v___x_1734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(32u);
v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_unsigned_to_nat(32u);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1740_);
v___x_1742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
lean_ctor_set(v___x_1743_, 2, v___x_1739_);
lean_ctor_set(v___x_1743_, 3, v___x_1739_);
lean_ctor_set_usize(v___x_1743_, 4, v___x_1738_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = lean_box(1);
v___x_1745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
lean_ctor_set(v___x_1747_, 2, v___x_1744_);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9));
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15));
v___x_1765_ = l_Lean_stringToMessageData(v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1769_, lean_object* v_declHint_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_env_1775_; uint8_t v___x_1776_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_st_ref_get(v___y_1771_);
v_env_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_env_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = l_Lean_Name_isAnonymous(v_declHint_1770_);
if (v___x_1776_ == 0)
{
uint8_t v_isExporting_1777_; 
v_isExporting_1777_ = lean_ctor_get_uint8(v_env_1775_, sizeof(void*)*13);
if (v_isExporting_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v_env_1775_);
lean_dec(v_declHint_1770_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_msg_1769_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
lean_inc_ref(v_env_1775_);
v___x_1779_ = l_Lean_Environment_setExporting(v_env_1775_, v___x_1776_);
lean_inc(v_declHint_1770_);
lean_inc_ref(v___x_1779_);
v___x_1780_ = l_Lean_Environment_contains(v___x_1779_, v_declHint_1770_, v_isExporting_1777_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_env_1775_);
lean_dec(v_declHint_1770_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_msg_1769_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_c_1787_; lean_object* v___x_1788_; 
v___x_1782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1784_ = l_Lean_Options_empty;
v___x_1785_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1779_);
lean_ctor_set(v___x_1785_, 1, v___x_1782_);
lean_ctor_set(v___x_1785_, 2, v___x_1783_);
lean_ctor_set(v___x_1785_, 3, v___x_1784_);
lean_inc(v_declHint_1770_);
v___x_1786_ = l_Lean_MessageData_ofConstName(v_declHint_1770_, v___x_1776_);
v_c_1787_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1787_, 0, v___x_1785_);
lean_ctor_set(v_c_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1775_, v_declHint_1770_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_env_1775_);
lean_dec(v_declHint_1770_);
v___x_1789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v_c_1787_);
v___x_1791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_MessageData_note(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_msg_1769_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1830_; 
v_val_1796_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1798_ = v___x_1788_;
v_isShared_1799_ = v_isSharedCheck_1830_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_val_1796_);
lean_dec(v___x_1788_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1830_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v_moduleNames_1801_; lean_object* v_mod_1802_; uint8_t v___x_1803_; 
v___x_1800_ = l_Lean_Environment_header(v_env_1775_);
lean_dec_ref(v_env_1775_);
v_moduleNames_1801_ = lean_ctor_get(v___x_1800_, 4);
lean_inc_ref(v_moduleNames_1801_);
lean_dec_ref(v___x_1800_);
v_mod_1802_ = lean_array_get(v___x_1773_, v_moduleNames_1801_, v_val_1796_);
lean_dec(v_val_1796_);
lean_dec_ref(v_moduleNames_1801_);
v___x_1803_ = l_Lean_isPrivateName(v_declHint_1770_);
lean_dec(v_declHint_1770_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_c_1787_);
v___x_1806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_MessageData_ofName(v_mod_1802_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_MessageData_note(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_msg_1769_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1813_);
v___x_1815_ = v___x_1798_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_c_1787_);
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_MessageData_ofName(v_mod_1802_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_MessageData_note(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_msg_1769_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1826_);
v___x_1828_ = v___x_1798_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1831_; 
lean_dec_ref(v_env_1775_);
lean_dec(v_declHint_1770_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_msg_1769_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1832_, lean_object* v_declHint_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1832_, v_declHint_1833_, v___y_1834_);
lean_dec(v___y_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_1837_, lean_object* v_declHint_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
v___x_1844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1837_, v_declHint_1838_, v___y_1842_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = l_Lean_unknownIdentifierMessageTag;
v___x_1850_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_a_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1855_, lean_object* v_declHint_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1855_, v_declHint_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_toCold_1870_; lean_object* v_currRecDepth_1871_; lean_object* v_ref_1872_; uint16_t v_optionFlags_1873_; uint8_t v_suppressElabErrors_1874_; uint8_t v_isRecordingDeps_1875_; lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_toCold_1870_ = lean_ctor_get(v___y_1867_, 0);
v_currRecDepth_1871_ = lean_ctor_get(v___y_1867_, 1);
v_ref_1872_ = lean_ctor_get(v___y_1867_, 2);
v_optionFlags_1873_ = lean_ctor_get_uint16(v___y_1867_, sizeof(void*)*3);
v_suppressElabErrors_1874_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1875_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3 + 3);
v_ref_1876_ = l_Lean_replaceRef(v_ref_1863_, v_ref_1872_);
lean_inc(v_currRecDepth_1871_);
lean_inc_ref(v_toCold_1870_);
v___x_1877_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1877_, 0, v_toCold_1870_);
lean_ctor_set(v___x_1877_, 1, v_currRecDepth_1871_);
lean_ctor_set(v___x_1877_, 2, v_ref_1876_);
lean_ctor_set_uint16(v___x_1877_, sizeof(void*)*3, v_optionFlags_1873_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*3 + 2, v_suppressElabErrors_1874_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*3 + 3, v_isRecordingDeps_1875_);
v___x_1878_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1864_, v___y_1865_, v___y_1866_, v___x_1877_, v___y_1868_);
lean_dec_ref_known(v___x_1877_, 3);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1879_, lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1879_, v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_ref_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1887_, lean_object* v_msg_1888_, lean_object* v_declHint_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_a_1896_; lean_object* v___x_1897_; 
v___x_1895_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1888_, v_declHint_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1887_, v_a_1896_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v_declHint_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1898_, v_msg_1899_, v_declHint_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_ref_1898_);
return v_res_1906_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1910_, lean_object* v_constName_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1917_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1918_ = 0;
lean_inc(v_constName_1911_);
v___x_1919_ = l_Lean_MessageData_ofConstName(v_constName_1911_, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1917_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1910_, v___x_1922_, v_constName_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1924_, lean_object* v_constName_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_1924_, v_constName_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v_ref_1924_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object* v_constName_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_ref_1938_; lean_object* v___x_1939_; 
v_ref_1938_ = lean_ctor_get(v___y_1935_, 2);
v___x_1939_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_1938_, v_constName_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object* v_constName_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v_env_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1953_ = lean_st_ref_get(v___y_1951_);
v_env_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc_ref(v_env_1954_);
lean_dec(v___x_1953_);
v___x_1955_ = 0;
lean_inc(v_constName_1947_);
v___x_1956_ = l_Lean_Environment_findConstVal_x3f(v_env_1954_, v_constName_1947_, v___x_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1957_;
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_constName_1947_);
v_val_1958_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 0);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_val_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object* v_constName_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_constName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__1(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__0));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__3(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__2));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object* v_declName_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; 
lean_inc(v_declName_1979_);
v___x_1985_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_declName_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2028_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2028_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2028_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1998_; lean_object* v_env_1999_; uint8_t v___x_2000_; 
v___x_1998_ = lean_st_ref_get(v_a_1983_);
v_env_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_ref(v_env_1999_);
lean_dec(v___x_1998_);
lean_inc(v_declName_1979_);
v___x_2000_ = l_Lean_wasOriginallyTheorem(v_env_1999_, v_declName_1979_);
if (v___x_2000_ == 0)
{
lean_object* v_type_2001_; lean_object* v___x_2002_; 
v_type_2001_ = lean_ctor_get(v_a_1986_, 2);
lean_inc_ref(v_type_2001_);
v___x_2002_ = l_Lean_Meta_isProp(v_type_2001_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; uint8_t v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = lean_unbox(v_a_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_del_object(v___x_1988_);
lean_dec(v_a_1986_);
v___x_2005_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__1, &l_Lean_Meta_Grind_getProofForDecl___closed__1_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__1);
v___x_2006_ = lean_unbox(v_a_2003_);
lean_dec(v_a_2003_);
v___x_2007_ = l_Lean_MessageData_ofConstName(v_declName_1979_, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__3, &l_Lean_Meta_Grind_getProofForDecl___closed__3_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__3);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_2010_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_dec(v_a_2003_);
goto v___jp_1990_;
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_del_object(v___x_1988_);
lean_dec(v_a_1986_);
lean_dec(v_declName_1979_);
v_a_2020_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2002_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2002_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
goto v___jp_1990_;
}
v___jp_1990_:
{
lean_object* v_levelParams_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v_levelParams_1991_ = lean_ctor_get(v_a_1986_, 1);
lean_inc(v_levelParams_1991_);
lean_dec(v_a_1986_);
v___x_1992_ = lean_box(0);
v___x_1993_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(v_levelParams_1991_, v___x_1992_);
v___x_1994_ = l_Lean_mkConst(v_declName_1979_, v___x_1993_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1994_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_declName_1979_);
v_a_2029_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1985_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1985_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object* v_declName_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object* v_00_u03b1_2044_, lean_object* v_constName_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_constName_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(v_00_u03b1_2052_, v_constName_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2060_, lean_object* v_ref_2061_, lean_object* v_constName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2061_, v_constName_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_ref_2070_, lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(v_00_u03b1_2069_, v_ref_2070_, v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v_ref_2070_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2078_, lean_object* v_ref_2079_, lean_object* v_msg_2080_, lean_object* v_declHint_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2079_, v_msg_2080_, v_declHint_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_ref_2089_, lean_object* v_msg_2090_, lean_object* v_declHint_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2088_, v_ref_2089_, v_msg_2090_, v_declHint_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_ref_2089_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2098_, lean_object* v_declHint_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2098_, v_declHint_2099_, v___y_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2106_, lean_object* v_declHint_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2106_, v_declHint_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2114_, lean_object* v_ref_2115_, lean_object* v_msg_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2115_, v_msg_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_ref_2124_, lean_object* v_msg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2123_, v_ref_2124_, v_msg_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v_ref_2124_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object* v___x_2132_, lean_object* v___x_2133_, lean_object* v_sym_2134_, lean_object* v_next_2135_, lean_object* v_acc_2136_, lean_object* v_h_2137_, lean_object* v_G_2138_){
_start:
{
lean_object* v_a_2140_; uint8_t v___x_2144_; 
v___x_2144_ = lean_nat_dec_lt(v_next_2135_, v___x_2132_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_G_2138_);
lean_dec(v_sym_2134_);
return v_acc_2136_;
}
else
{
lean_object* v_fst_2145_; lean_object* v_snd_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2175_; 
v_fst_2145_ = lean_ctor_get(v_acc_2136_, 0);
v_snd_2146_ = lean_ctor_get(v_acc_2136_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_acc_2136_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2148_ = v_acc_2136_;
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_snd_2146_);
lean_inc(v_fst_2145_);
lean_dec(v_acc_2136_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v_smap_2151_; lean_object* v_origins_2152_; lean_object* v_erased_2153_; lean_object* v_omap_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2174_; 
v___x_2150_ = lean_array_get(v___x_2133_, v_snd_2146_, v_next_2135_);
v_smap_2151_ = lean_ctor_get(v___x_2150_, 0);
v_origins_2152_ = lean_ctor_get(v___x_2150_, 1);
v_erased_2153_ = lean_ctor_get(v___x_2150_, 2);
v_omap_2154_ = lean_ctor_get(v___x_2150_, 3);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2156_ = v___x_2150_;
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_omap_2154_);
lean_inc(v_erased_2153_);
lean_inc(v_origins_2152_);
lean_inc(v_smap_2151_);
lean_dec(v___x_2150_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2174_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_2134_);
v___x_2160_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2158_, v___x_2159_, v_smap_2151_, v_sym_2134_);
if (lean_obj_tag(v___x_2160_) == 1)
{
lean_object* v_val_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v_val_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = l_Lean_PersistentHashMap_erase___redArg(v___x_2158_, v___x_2159_, v_smap_2151_, v_sym_2134_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2162_);
v___x_2164_ = v___x_2156_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_origins_2152_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_erased_2153_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_omap_2154_);
v___x_2164_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = l_List_appendTR___redArg(v_fst_2145_, v_val_2161_);
v___x_2166_ = lean_array_set(v_snd_2146_, v_next_2135_, v___x_2164_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2166_);
lean_ctor_set(v___x_2148_, 0, v___x_2165_);
v___x_2168_ = v___x_2148_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v_a_2140_ = v___x_2168_;
goto v___jp_2139_;
}
}
}
else
{
lean_object* v___x_2172_; 
lean_dec(v___x_2160_);
lean_del_object(v___x_2156_);
lean_dec_ref(v_omap_2154_);
lean_dec_ref(v_erased_2153_);
lean_dec_ref(v_origins_2152_);
lean_dec_ref(v_smap_2151_);
lean_dec(v_sym_2134_);
if (v_isShared_2149_ == 0)
{
v___x_2172_ = v___x_2148_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_fst_2145_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_snd_2146_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_a_2140_ = v___x_2172_;
goto v___jp_2139_;
}
}
}
}
}
v___jp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = lean_nat_add(v_next_2135_, v___x_2141_);
v___x_2143_ = lean_apply_4(v_G_2138_, v___x_2142_, v_a_2140_, lean_box(0), lean_box(0));
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v_sym_2178_, lean_object* v_next_2179_, lean_object* v_acc_2180_, lean_object* v_h_2181_, lean_object* v_G_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(v___x_2176_, v___x_2177_, v_sym_2178_, v_next_2179_, v_acc_2180_, v_h_2181_, v_G_2182_);
lean_dec(v_next_2179_);
lean_dec_ref(v___x_2177_);
lean_dec(v___x_2176_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object* v_s_2184_, lean_object* v_sym_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___x_2189_; lean_object* v_result_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2204_; 
v___x_2186_ = lean_array_get_size(v_s_2184_);
v___x_2187_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
v___f_2188_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2188_, 0, v___x_2186_);
lean_closure_set(v___f_2188_, 1, v___x_2187_);
lean_closure_set(v___f_2188_, 2, v_sym_2185_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_result_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_result_2190_);
lean_ctor_set(v___x_2191_, 1, v_s_2184_);
v___x_2192_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2188_, v___x_2189_, v___x_2191_, lean_box(0));
v_fst_2193_ = lean_ctor_get(v___x_2192_, 0);
v_snd_2194_ = lean_ctor_get(v___x_2192_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2196_ = v___x_2192_;
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_snd_2194_);
lean_inc(v_fst_2193_);
lean_dec(v___x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2204_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
uint8_t v___x_2198_; 
v___x_2198_ = l_List_isEmpty___redArg(v_fst_2193_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2200_; 
if (v_isShared_2197_ == 0)
{
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_fst_2193_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_snd_2194_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
else
{
lean_object* v___x_2203_; 
lean_del_object(v___x_2196_);
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
v___x_2203_ = lean_box(0);
return v___x_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object* v_00_u03b1_2205_, lean_object* v_s_2206_, lean_object* v_sym_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(v_s_2206_, v_sym_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_thms_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0);
v___x_2211_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0);
v_thms_2212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_thms_2212_, 0, v___x_2211_);
lean_ctor_set(v_thms_2212_, 1, v___x_2210_);
lean_ctor_set(v_thms_2212_, 2, v___x_2210_);
lean_ctor_set(v_thms_2212_, 3, v___x_2211_);
return v_thms_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object* v_inst_2213_, lean_object* v_s_2214_, lean_object* v_thm_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2216_ = lean_array_get_size(v_s_2214_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_nat_dec_eq(v___x_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_nat_dec_lt(v___x_2217_, v___x_2216_);
if (v___x_2219_ == 0)
{
lean_dec(v_thm_2215_);
lean_dec_ref(v_inst_2213_);
return v_s_2214_;
}
else
{
lean_object* v_v_2220_; lean_object* v___x_2221_; lean_object* v_xs_x27_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_v_2220_ = lean_array_fget(v_s_2214_, v___x_2217_);
v___x_2221_ = lean_box(0);
v_xs_x27_2222_ = lean_array_fset(v_s_2214_, v___x_2217_, v___x_2221_);
v___x_2223_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2213_, v_v_2220_, v_thm_2215_);
v___x_2224_ = lean_array_fset(v_xs_x27_2222_, v___x_2217_, v___x_2223_);
return v___x_2224_;
}
}
else
{
lean_object* v_thms_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v_s_2214_);
v_thms_2225_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1);
v___x_2226_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2213_, v_thms_2225_, v_thm_2215_);
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_mk_empty_array_with_capacity(v___x_2227_);
v___x_2229_ = lean_array_push(v___x_2228_, v___x_2226_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object* v_00_u03b1_2230_, lean_object* v_inst_2231_, lean_object* v_s_2232_, lean_object* v_thm_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Meta_Grind_TheoremsArray_insert___redArg(v_inst_2231_, v_s_2232_, v_thm_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object* v_origin_2235_, lean_object* v_as_2236_, size_t v_i_2237_, size_t v_stop_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_eq(v_i_2237_, v_stop_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v_erased_2241_; uint8_t v___x_2242_; 
v___x_2240_ = lean_array_uget_borrowed(v_as_2236_, v_i_2237_);
v_erased_2241_ = lean_ctor_get(v___x_2240_, 2);
v___x_2242_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_2241_, v_origin_2235_);
if (v___x_2242_ == 0)
{
size_t v___x_2243_; size_t v___x_2244_; 
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2237_, v___x_2243_);
v_i_2237_ = v___x_2244_;
goto _start;
}
else
{
return v___x_2242_;
}
}
else
{
uint8_t v___x_2246_; 
v___x_2246_ = 0;
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object* v_origin_2247_, lean_object* v_as_2248_, lean_object* v_i_2249_, lean_object* v_stop_2250_){
_start:
{
size_t v_i_boxed_2251_; size_t v_stop_boxed_2252_; uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_i_boxed_2251_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_stop_boxed_2252_ = lean_unbox_usize(v_stop_2250_);
lean_dec(v_stop_2250_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2247_, v_as_2248_, v_i_boxed_2251_, v_stop_boxed_2252_);
lean_dec_ref(v_as_2248_);
lean_dec_ref(v_origin_2247_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object* v_s_2255_, lean_object* v_origin_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = lean_array_get_size(v_s_2255_);
v___x_2259_ = lean_nat_dec_lt(v___x_2257_, v___x_2258_);
if (v___x_2259_ == 0)
{
return v___x_2259_;
}
else
{
if (v___x_2259_ == 0)
{
return v___x_2259_;
}
else
{
size_t v___x_2260_; size_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2260_ = ((size_t)0ULL);
v___x_2261_ = lean_usize_of_nat(v___x_2258_);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2256_, v_s_2255_, v___x_2260_, v___x_2261_);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object* v_s_2263_, lean_object* v_origin_2264_){
_start:
{
uint8_t v_res_2265_; lean_object* v_r_2266_; 
v_res_2265_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2263_, v_origin_2264_);
lean_dec_ref(v_origin_2264_);
lean_dec_ref(v_s_2263_);
v_r_2266_ = lean_box(v_res_2265_);
return v_r_2266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object* v_00_u03b1_2267_, lean_object* v_s_2268_, lean_object* v_origin_2269_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2268_, v_origin_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_s_2272_, lean_object* v_origin_2273_){
_start:
{
uint8_t v_res_2274_; lean_object* v_r_2275_; 
v_res_2274_ = l_Lean_Meta_Grind_TheoremsArray_isErased(v_00_u03b1_2271_, v_s_2272_, v_origin_2273_);
lean_dec_ref(v_origin_2273_);
lean_dec_ref(v_s_2272_);
v_r_2275_ = lean_box(v_res_2274_);
return v_r_2275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object* v_00_u03b1_2276_, lean_object* v_origin_2277_, lean_object* v_as_2278_, size_t v_i_2279_, size_t v_stop_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2277_, v_as_2278_, v_i_2279_, v_stop_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_origin_2283_, lean_object* v_as_2284_, lean_object* v_i_2285_, lean_object* v_stop_2286_){
_start:
{
size_t v_i_boxed_2287_; size_t v_stop_boxed_2288_; uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_i_boxed_2287_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_stop_boxed_2288_ = lean_unbox_usize(v_stop_2286_);
lean_dec(v_stop_2286_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(v_00_u03b1_2282_, v_origin_2283_, v_as_2284_, v_i_boxed_2287_, v_stop_boxed_2288_);
lean_dec_ref(v_as_2284_);
lean_dec_ref(v_origin_2283_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object* v_upperBound_2291_, lean_object* v_s_2292_, lean_object* v_origin_2293_, lean_object* v_a_2294_, lean_object* v_b_2295_){
_start:
{
lean_object* v_a_2297_; uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_lt(v_a_2294_, v_upperBound_2291_);
if (v___x_2301_ == 0)
{
lean_dec(v_a_2294_);
return v_b_2295_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2302_ = lean_array_fget_borrowed(v_s_2292_, v_a_2294_);
v___x_2303_ = l_Lean_Meta_Grind_Theorems_find___redArg(v___x_2302_, v_origin_2293_);
v___x_2304_ = l_List_isEmpty___redArg(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = l_List_appendTR___redArg(v_b_2295_, v___x_2303_);
v_a_2297_ = v___x_2305_;
goto v___jp_2296_;
}
else
{
lean_dec(v___x_2303_);
v_a_2297_ = v_b_2295_;
goto v___jp_2296_;
}
}
v___jp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_add(v_a_2294_, v___x_2298_);
lean_dec(v_a_2294_);
v_a_2294_ = v___x_2299_;
v_b_2295_ = v_a_2297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_2306_, lean_object* v_s_2307_, lean_object* v_origin_2308_, lean_object* v_a_2309_, lean_object* v_b_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2306_, v_s_2307_, v_origin_2308_, v_a_2309_, v_b_2310_);
lean_dec_ref(v_origin_2308_);
lean_dec_ref(v_s_2307_);
lean_dec(v_upperBound_2306_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object* v_s_2312_, lean_object* v_origin_2313_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_r_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_array_get_size(v_s_2312_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v_r_2316_ = lean_box(0);
v___x_2317_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v___x_2314_, v_s_2312_, v_origin_2313_, v___x_2315_, v_r_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object* v_s_2318_, lean_object* v_origin_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2318_, v_origin_2319_);
lean_dec_ref(v_origin_2319_);
lean_dec_ref(v_s_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object* v_00_u03b1_2321_, lean_object* v_s_2322_, lean_object* v_origin_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2322_, v_origin_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object* v_00_u03b1_2325_, lean_object* v_s_2326_, lean_object* v_origin_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Meta_Grind_TheoremsArray_find(v_00_u03b1_2325_, v_s_2326_, v_origin_2327_);
lean_dec_ref(v_origin_2327_);
lean_dec_ref(v_s_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object* v_00_u03b1_2329_, lean_object* v_upperBound_2330_, lean_object* v_s_2331_, lean_object* v_origin_2332_, lean_object* v_inst_2333_, lean_object* v_R_2334_, lean_object* v_a_2335_, lean_object* v_b_2336_, lean_object* v_c_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2330_, v_s_2331_, v_origin_2332_, v_a_2335_, v_b_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object* v_00_u03b1_2339_, lean_object* v_upperBound_2340_, lean_object* v_s_2341_, lean_object* v_origin_2342_, lean_object* v_inst_2343_, lean_object* v_R_2344_, lean_object* v_a_2345_, lean_object* v_b_2346_, lean_object* v_c_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(v_00_u03b1_2339_, v_upperBound_2340_, v_s_2341_, v_origin_2342_, v_inst_2343_, v_R_2344_, v_a_2345_, v_b_2346_, v_c_2347_);
lean_dec_ref(v_origin_2342_);
lean_dec_ref(v_s_2341_);
lean_dec(v_upperBound_2340_);
return v_res_2348_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
}
#ifdef __cplusplus
}
#endif
