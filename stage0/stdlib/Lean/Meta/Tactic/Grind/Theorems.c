// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Theorems
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic import Lean.Meta.Eqns import Init.Data.Range.Polymorphic.Iterators
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_getConstVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26;
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
uint8_t l_Lean_Meta_Grind_instBEqOrigin___lam__0(lean_object* v_a_181_, lean_object* v_b_182_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqOrigin___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_181_ = stack[0].m_obj;
lean_object* v_b_182_ = stack[1].m_obj;
uint8_t v_res_188_;
v_res_188_ = l_Lean_Meta_Grind_instBEqOrigin___lam__0(v_a_181_, v_b_182_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Meta_Grind_instBEqOrigin___lam__0(v_a_189_, v_b_190_);
lean_dec_ref(v_b_190_);
lean_dec_ref(v_a_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object* v_a_195_){
_start:
{
lean_object* v___y_197_; lean_object* v_declName_200_; 
v_declName_200_ = lean_ctor_get(v_a_195_, 0);
v___y_197_ = v_declName_200_;
goto v___jp_196_;
v___jp_196_:
{
if (lean_obj_tag(v___y_197_) == 0)
{
uint64_t v___x_198_; 
v___x_198_ = 1723ULL;
return v___x_198_;
}
else
{
uint64_t v_hash_199_; 
v_hash_199_ = lean_ctor_get_uint64(v___y_197_, sizeof(void*)*2);
return v_hash_199_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instHashableOrigin___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_195_ = stack[0].m_obj;
uint64_t v_res_201_;
v_res_201_ = l_Lean_Meta_Grind_instHashableOrigin___lam__0(v_a_195_);
stack->m_num = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object* v_a_202_){
_start:
{
uint64_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_Grind_instHashableOrigin___lam__0(v_a_202_);
lean_dec_ref(v_a_202_);
v_r_204_ = lean_box_uint64(v_res_203_);
return v_r_204_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg(){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__1);
return v___x_211_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_212_;
v_res_212_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___boxed(lean_object* v___dummy_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
return v_res_214_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg();
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_object* v_00_u03b2_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
v___x_221_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_220_);
lean_ctor_set(v___x_222_, 3, v___x_221_);
return v___x_222_;
}
}
lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg(){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1);
return v___x_224_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_225_;
v_res_225_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___boxed(lean_object* v___dummy_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object* v_00_u03b1_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_230_;
}
}
lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg(){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_232_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instInhabitedTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_233_;
v_res_233_ = l_Lean_Meta_Grind_instInhabitedTheorems___redArg();
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___redArg___boxed(lean_object* v___dummy_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_Grind_instInhabitedTheorems___redArg();
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems(lean_object* v_a_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9));
v___x_259_ = l_instInhabitedOfMonad___redArg(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13));
v___x_264_ = lean_unsigned_to_nat(6u);
v___x_265_ = lean_unsigned_to_nat(82u);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12));
v___x_267_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11));
v___x_268_ = l_mkPanicMessageWithDecl(v___x_267_, v___x_266_, v___x_265_, v___x_264_, v___x_263_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg(lean_object* v_inst_271_, lean_object* v_s_272_, lean_object* v_thm_273_){
_start:
{
lean_object* v_getSymbols_274_; lean_object* v_setSymbols_275_; lean_object* v_getOrigin_276_; lean_object* v___x_277_; lean_object* v___x_281_; 
v_getSymbols_274_ = lean_ctor_get(v_inst_271_, 0);
lean_inc_ref(v_getSymbols_274_);
v_setSymbols_275_ = lean_ctor_get(v_inst_271_, 1);
lean_inc(v_setSymbols_275_);
v_getOrigin_276_ = lean_ctor_get(v_inst_271_, 2);
lean_inc_ref(v_getOrigin_276_);
lean_dec_ref(v_inst_271_);
v___x_277_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10);
lean_inc(v_thm_273_);
v___x_281_ = lean_apply_1(v_getSymbols_274_, v_thm_273_);
if (lean_obj_tag(v___x_281_) == 1)
{
lean_object* v_head_282_; 
v_head_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_head_282_);
if (lean_obj_tag(v_head_282_) == 2)
{
lean_object* v_tail_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_331_; 
v_tail_283_ = lean_ctor_get(v___x_281_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_332_);
v___x_285_ = v___x_281_;
v_isShared_286_ = v_isSharedCheck_331_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_tail_283_);
lean_dec(v___x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_331_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_constName_287_; lean_object* v_smap_288_; lean_object* v_origins_289_; lean_object* v_erased_290_; lean_object* v_omap_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_330_; 
v_constName_287_ = lean_ctor_get(v_head_282_, 0);
lean_inc(v_constName_287_);
lean_dec_ref_known(v_head_282_, 1);
v_smap_288_ = lean_ctor_get(v_s_272_, 0);
v_origins_289_ = lean_ctor_get(v_s_272_, 1);
v_erased_290_ = lean_ctor_get(v_s_272_, 2);
v_omap_291_ = lean_ctor_get(v_s_272_, 3);
v_isSharedCheck_330_ = !lean_is_exclusive(v_s_272_);
if (v_isSharedCheck_330_ == 0)
{
v___x_293_ = v_s_272_;
v_isShared_294_ = v_isSharedCheck_330_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_omap_291_);
lean_inc(v_erased_290_);
lean_inc(v_origins_289_);
lean_inc(v_smap_288_);
lean_dec(v_s_272_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_330_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_thm_299_; lean_object* v_origin_300_; lean_object* v___x_301_; lean_object* v_origins_302_; lean_object* v_erased_303_; lean_object* v___y_305_; lean_object* v___x_323_; 
v___f_295_ = ((lean_object*)(l_Lean_Meta_Grind_instBEqOrigin___closed__0));
v___f_296_ = ((lean_object*)(l_Lean_Meta_Grind_instHashableOrigin___closed__0));
v___x_297_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_298_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
v_thm_299_ = lean_apply_2(v_setSymbols_275_, v_thm_273_, v_tail_283_);
lean_inc(v_thm_299_);
v_origin_300_ = lean_apply_1(v_getOrigin_276_, v_thm_299_);
v___x_301_ = lean_box(0);
lean_inc_ref_n(v_origin_300_, 2);
v_origins_302_ = l_Lean_PersistentHashMap_insert___redArg(v___f_295_, v___f_296_, v_origins_289_, v_origin_300_, v___x_301_);
v_erased_303_ = l_Lean_PersistentHashMap_erase___redArg(v___f_295_, v___f_296_, v_erased_290_, v_origin_300_);
lean_inc(v_constName_287_);
v___x_323_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_297_, v___x_298_, v_smap_288_, v_constName_287_);
if (lean_obj_tag(v___x_323_) == 1)
{
lean_object* v_val_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_val_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v___x_323_, 1);
lean_inc(v_thm_299_);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v_thm_299_);
lean_ctor_set(v___x_325_, 1, v_val_324_);
v___x_326_ = l_Lean_PersistentHashMap_insert___redArg(v___x_297_, v___x_298_, v_smap_288_, v_constName_287_, v___x_325_);
v___y_305_ = v___x_326_;
goto v___jp_304_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v___x_323_);
v___x_327_ = lean_box(0);
lean_inc(v_thm_299_);
v___x_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_328_, 0, v_thm_299_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_PersistentHashMap_insert___redArg(v___x_297_, v___x_298_, v_smap_288_, v_constName_287_, v___x_328_);
v___y_305_ = v___x_329_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_306_; 
lean_inc_ref(v_origin_300_);
v___x_306_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_295_, v___f_296_, v_omap_291_, v_origin_300_);
if (lean_obj_tag(v___x_306_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_309_; 
v_val_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_307_);
lean_dec_ref_known(v___x_306_, 1);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_val_307_);
lean_ctor_set(v___x_285_, 0, v_thm_299_);
v___x_309_ = v___x_285_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_thm_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_val_307_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_PersistentHashMap_insert___redArg(v___f_295_, v___f_296_, v_omap_291_, v_origin_300_, v___x_309_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 3, v___x_310_);
lean_ctor_set(v___x_293_, 2, v_erased_303_);
lean_ctor_set(v___x_293_, 1, v_origins_302_);
lean_ctor_set(v___x_293_, 0, v___y_305_);
v___x_312_ = v___x_293_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___y_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_origins_302_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_erased_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v___x_310_);
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
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v___x_306_);
v___x_315_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_315_);
lean_ctor_set(v___x_285_, 0, v_thm_299_);
v___x_317_ = v___x_285_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_thm_299_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_322_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_PersistentHashMap_insert___redArg(v___f_295_, v___f_296_, v_omap_291_, v_origin_300_, v___x_317_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 3, v___x_318_);
lean_ctor_set(v___x_293_, 2, v_erased_303_);
lean_ctor_set(v___x_293_, 1, v_origins_302_);
lean_ctor_set(v___x_293_, 0, v___y_305_);
v___x_320_ = v___x_293_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___y_305_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_origins_302_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_erased_303_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_281_, 2);
lean_dec(v_head_282_);
lean_dec_ref(v_getOrigin_276_);
lean_dec(v_setSymbols_275_);
lean_dec(v_thm_273_);
lean_dec_ref(v_s_272_);
goto v___jp_278_;
}
}
else
{
lean_dec(v___x_281_);
lean_dec_ref(v_getOrigin_276_);
lean_dec(v_setSymbols_275_);
lean_dec(v_thm_273_);
lean_dec_ref(v_s_272_);
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14);
v___x_280_ = l_panic___redArg(v___x_277_, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_s_335_, lean_object* v_thm_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_334_, v_s_335_, v_thm_336_);
return v___x_337_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_338_, lean_object* v_i_339_, lean_object* v_k_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___y_344_; lean_object* v___y_345_; 
v___x_341_ = lean_array_get_size(v_keys_338_);
v___x_342_ = lean_nat_dec_lt(v_i_339_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v_i_339_);
return v___x_342_;
}
else
{
lean_object* v_k_x27_350_; lean_object* v___y_352_; lean_object* v_declName_354_; 
v_k_x27_350_ = lean_array_fget_borrowed(v_keys_338_, v_i_339_);
v_declName_354_ = lean_ctor_get(v_k_340_, 0);
v___y_352_ = v_declName_354_;
goto v___jp_351_;
v___jp_351_:
{
lean_object* v_declName_353_; 
v_declName_353_ = lean_ctor_get(v_k_x27_350_, 0);
v___y_344_ = v___y_352_;
v___y_345_ = v_declName_353_;
goto v___jp_343_;
}
}
v___jp_343_:
{
uint8_t v___x_346_; 
v___x_346_ = lean_name_eq(v___y_344_, v___y_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_i_339_, v___x_347_);
lean_dec(v_i_339_);
v_i_339_ = v___x_348_;
goto _start;
}
else
{
lean_dec(v_i_339_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_338_ = stack[0].m_obj;
lean_object* v_i_339_ = stack[1].m_obj;
lean_object* v_k_340_ = stack[2].m_obj;
uint8_t v_res_355_;
v_res_355_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_338_, v_i_339_, v_k_340_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_356_, lean_object* v_i_357_, lean_object* v_k_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_356_, v_i_357_, v_k_358_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_keys_356_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object* v_x_361_, size_t v_x_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v_es_364_; lean_object* v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v_j_368_; lean_object* v___x_369_; 
v_es_364_ = lean_ctor_get(v_x_361_, 0);
v___x_365_ = lean_box(2);
v___x_366_ = ((size_t)31ULL);
v___x_367_ = lean_usize_land(v_x_362_, v___x_366_);
v_j_368_ = lean_usize_to_nat(v___x_367_);
v___x_369_ = lean_array_get_borrowed(v___x_365_, v_es_364_, v_j_368_);
lean_dec(v_j_368_);
switch(lean_obj_tag(v___x_369_))
{
case 0:
{
lean_object* v_key_370_; lean_object* v___y_372_; lean_object* v_declName_375_; 
v_key_370_ = lean_ctor_get(v___x_369_, 0);
v_declName_375_ = lean_ctor_get(v_x_363_, 0);
v___y_372_ = v_declName_375_;
goto v___jp_371_;
v___jp_371_:
{
lean_object* v_declName_373_; uint8_t v___x_374_; 
v_declName_373_ = lean_ctor_get(v_key_370_, 0);
v___x_374_ = lean_name_eq(v___y_372_, v_declName_373_);
return v___x_374_;
}
}
case 1:
{
lean_object* v_node_376_; size_t v___x_377_; size_t v___x_378_; 
v_node_376_ = lean_ctor_get(v___x_369_, 0);
v___x_377_ = ((size_t)5ULL);
v___x_378_ = lean_usize_shift_right(v_x_362_, v___x_377_);
v_x_361_ = v_node_376_;
v_x_362_ = v___x_378_;
goto _start;
}
default: 
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
}
}
else
{
lean_object* v_ks_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_ks_381_ = lean_ctor_get(v_x_361_, 0);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_ks_381_, v___x_382_, v_x_363_);
return v___x_383_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_361_ = stack[0].m_obj;
size_t v_x_362_ = stack[1].m_num;
lean_object* v_x_363_ = stack[2].m_obj;
uint8_t v_res_384_;
v_res_384_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_361_, v_x_362_, v_x_363_);
stack->m_num = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
size_t v_x_216__boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_x_216__boxed_388_ = lean_unbox_usize(v_x_386_);
lean_dec(v_x_386_);
v_res_389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_385_, v_x_216__boxed_388_, v_x_387_);
lean_dec_ref(v_x_387_);
lean_dec_ref(v_x_385_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
uint64_t v___y_394_; lean_object* v___y_398_; lean_object* v_declName_401_; 
v_declName_401_ = lean_ctor_get(v_x_392_, 0);
v___y_398_ = v_declName_401_;
goto v___jp_397_;
v___jp_393_:
{
size_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_uint64_to_usize(v___y_394_);
v___x_396_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_391_, v___x_395_, v_x_392_);
return v___x_396_;
}
v___jp_397_:
{
if (lean_obj_tag(v___y_398_) == 0)
{
uint64_t v___x_399_; 
v___x_399_ = 1723ULL;
v___y_394_ = v___x_399_;
goto v___jp_393_;
}
else
{
uint64_t v_hash_400_; 
v_hash_400_ = lean_ctor_get_uint64(v___y_398_, sizeof(void*)*2);
v___y_394_ = v_hash_400_;
goto v___jp_393_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_391_ = stack[0].m_obj;
lean_object* v_x_392_ = stack[1].m_obj;
uint8_t v_res_402_;
v_res_402_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_391_, v_x_392_);
stack->m_num = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_403_, v_x_404_);
lean_dec_ref(v_x_404_);
lean_dec_ref(v_x_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object* v_s_407_, lean_object* v_origin_408_){
_start:
{
lean_object* v_origins_409_; uint8_t v___x_410_; 
v_origins_409_ = lean_ctor_get(v_s_407_, 1);
v___x_410_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_origins_409_, v_origin_408_);
return v___x_410_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_407_ = stack[0].m_obj;
lean_object* v_origin_408_ = stack[1].m_obj;
uint8_t v_res_411_;
v_res_411_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_407_, v_origin_408_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object* v_s_412_, lean_object* v_origin_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_412_, v_origin_413_);
lean_dec_ref(v_origin_413_);
lean_dec_ref(v_s_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object* v_00_u03b1_416_, lean_object* v_s_417_, lean_object* v_origin_418_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_417_, v_origin_418_);
return v___x_419_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_417_ = stack[1].m_obj;
lean_object* v_origin_418_ = stack[2].m_obj;
uint8_t v_res_420_;
v_res_420_ = l_Lean_Meta_Grind_Theorems_contains(lean_box(0), v_s_417_, v_origin_418_);
stack->m_num = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object* v_00_u03b1_421_, lean_object* v_s_422_, lean_object* v_origin_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_Meta_Grind_Theorems_contains(v_00_u03b1_421_, v_s_422_, v_origin_423_);
lean_dec_ref(v_origin_423_);
lean_dec_ref(v_s_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_427_ = stack[1].m_obj;
lean_object* v_x_428_ = stack[2].m_obj;
uint8_t v_res_430_;
v_res_430_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_box(0), v_x_427_, v_x_428_);
stack->m_num = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(v_00_u03b2_431_, v_x_432_, v_x_433_);
lean_dec_ref(v_x_433_);
lean_dec_ref(v_x_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, size_t v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_437_, v_x_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_437_ = stack[1].m_obj;
size_t v_x_438_ = stack[2].m_num;
lean_object* v_x_439_ = stack[3].m_obj;
uint8_t v_res_441_;
v_res_441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_box(0), v_x_437_, v_x_438_, v_x_439_);
stack->m_num = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
size_t v_x_358__boxed_446_; uint8_t v_res_447_; lean_object* v_r_448_; 
v_x_358__boxed_446_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_res_447_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(v_00_u03b2_442_, v_x_443_, v_x_358__boxed_446_, v_x_445_);
lean_dec_ref(v_x_445_);
lean_dec_ref(v_x_443_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_449_, lean_object* v_keys_450_, lean_object* v_vals_451_, lean_object* v_heq_452_, lean_object* v_i_453_, lean_object* v_k_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_450_, v_i_453_, v_k_454_);
return v___x_455_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_450_ = stack[1].m_obj;
lean_object* v_vals_451_ = stack[2].m_obj;
lean_object* v_i_453_ = stack[4].m_obj;
lean_object* v_k_454_ = stack[5].m_obj;
uint8_t v_res_456_;
v_res_456_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_box(0), v_keys_450_, v_vals_451_, lean_box(0), v_i_453_, v_k_454_);
stack->m_num = v_res_456_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_457_, lean_object* v_keys_458_, lean_object* v_vals_459_, lean_object* v_heq_460_, lean_object* v_i_461_, lean_object* v_k_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(v_00_u03b2_457_, v_keys_458_, v_vals_459_, v_heq_460_, v_i_461_, v_k_462_);
lean_dec_ref(v_k_462_);
lean_dec_ref(v_vals_459_);
lean_dec_ref(v_keys_458_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_465_, lean_object* v_v_466_, lean_object* v_i_467_){
_start:
{
lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_477_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_xs_465_);
v___x_480_ = lean_nat_dec_lt(v_i_467_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec(v_i_467_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v_declName_483_; 
v___x_482_ = lean_array_fget_borrowed(v_xs_465_, v_i_467_);
v_declName_483_ = lean_ctor_get(v___x_482_, 0);
v___y_477_ = v_declName_483_;
goto v___jp_476_;
}
v___jp_468_:
{
uint8_t v___x_471_; 
v___x_471_ = lean_name_eq(v___y_469_, v___y_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_i_467_, v___x_472_);
lean_dec(v_i_467_);
v_i_467_ = v___x_473_;
goto _start;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_i_467_);
return v___x_475_;
}
}
v___jp_476_:
{
lean_object* v_declName_478_; 
v_declName_478_ = lean_ctor_get(v_v_466_, 0);
v___y_469_ = v___y_477_;
v___y_470_ = v_declName_478_;
goto v___jp_468_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_484_, lean_object* v_v_485_, lean_object* v_i_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_484_, v_v_485_, v_i_486_);
lean_dec_ref(v_v_485_);
lean_dec_ref(v_xs_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object* v_xs_488_, lean_object* v_v_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_488_, v_v_489_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_492_, lean_object* v_v_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_xs_492_, v_v_493_);
lean_dec_ref(v_v_493_);
lean_dec_ref(v_xs_492_);
return v_res_494_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object* v_x_495_, size_t v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_es_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v_j_502_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v_entry_516_; 
v_es_498_ = lean_ctor_get(v_x_495_, 0);
v___x_499_ = lean_box(2);
v___x_500_ = ((size_t)31ULL);
v___x_501_ = lean_usize_land(v_x_496_, v___x_500_);
v_j_502_ = lean_usize_to_nat(v___x_501_);
v_entry_516_ = lean_array_get(v___x_499_, v_es_498_, v_j_502_);
switch(lean_obj_tag(v_entry_516_))
{
case 0:
{
lean_object* v_key_517_; lean_object* v___y_519_; lean_object* v_declName_521_; 
v_key_517_ = lean_ctor_get(v_entry_516_, 0);
lean_inc(v_key_517_);
lean_dec_ref_known(v_entry_516_, 2);
v_declName_521_ = lean_ctor_get(v_x_497_, 0);
v___y_519_ = v_declName_521_;
goto v___jp_518_;
v___jp_518_:
{
lean_object* v_declName_520_; 
v_declName_520_ = lean_ctor_get(v_key_517_, 0);
lean_inc(v_declName_520_);
lean_dec(v_key_517_);
v___y_504_ = v___y_519_;
v___y_505_ = v_declName_520_;
goto v___jp_503_;
}
}
case 1:
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_556_; 
lean_inc_ref(v_es_498_);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_557_);
v___x_523_ = v_x_495_;
v_isShared_524_ = v_isSharedCheck_556_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_x_495_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_556_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_node_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_555_; 
v_node_525_ = lean_ctor_get(v_entry_516_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_entry_516_);
if (v_isSharedCheck_555_ == 0)
{
v___x_527_ = v_entry_516_;
v_isShared_528_ = v_isSharedCheck_555_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_node_525_);
lean_dec(v_entry_516_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_555_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
size_t v___x_529_; lean_object* v_entries_530_; size_t v___x_531_; lean_object* v_newNode_532_; lean_object* v___x_533_; 
v___x_529_ = ((size_t)5ULL);
v_entries_530_ = lean_array_set(v_es_498_, v_j_502_, v___x_499_);
v___x_531_ = lean_usize_shift_right(v_x_496_, v___x_529_);
v_newNode_532_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_node_525_, v___x_531_, v_x_497_);
lean_inc_ref(v_newNode_532_);
v___x_533_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_535_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_newNode_532_);
v___x_535_ = v___x_527_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_newNode_532_);
v___x_535_ = v_reuseFailAlloc_540_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_set(v_entries_530_, v_j_502_, v___x_535_);
lean_dec(v_j_502_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_536_);
v___x_538_ = v___x_523_;
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
else
{
lean_object* v_val_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_newNode_532_);
lean_del_object(v___x_527_);
v_val_541_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_533_, 1);
v_fst_542_ = lean_ctor_get(v_val_541_, 0);
v_snd_543_ = lean_ctor_get(v_val_541_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_val_541_);
if (v_isSharedCheck_554_ == 0)
{
v___x_545_ = v_val_541_;
v_isShared_546_ = v_isSharedCheck_554_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snd_543_);
lean_inc(v_fst_542_);
lean_dec(v_val_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_554_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_542_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_snd_543_);
v___x_548_ = v_reuseFailAlloc_553_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_set(v_entries_530_, v_j_502_, v___x_548_);
lean_dec(v_j_502_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_549_);
v___x_551_ = v___x_523_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_502_);
return v_x_495_;
}
}
v___jp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = lean_name_eq(v___y_504_, v___y_505_);
lean_dec(v___y_505_);
if (v___x_506_ == 0)
{
lean_dec(v_j_502_);
return v_x_495_;
}
else
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
lean_inc_ref(v_es_498_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_515_);
v___x_508_ = v_x_495_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_x_495_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_array_set(v_es_498_, v_j_502_, v___x_499_);
lean_dec(v_j_502_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v_ks_558_; lean_object* v_vs_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_573_; 
v_ks_558_ = lean_ctor_get(v_x_495_, 0);
v_vs_559_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_573_ == 0)
{
v___x_561_ = v_x_495_;
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_vs_559_);
lean_inc(v_ks_558_);
lean_dec(v_x_495_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; 
v___x_563_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_ks_558_, v_x_497_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_565_; 
if (v_isShared_562_ == 0)
{
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_ks_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_vs_559_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v_val_567_; lean_object* v_keys_x27_568_; lean_object* v_vals_x27_569_; lean_object* v___x_571_; 
v_val_567_ = lean_ctor_get(v___x_563_, 0);
lean_inc_n(v_val_567_, 2);
lean_dec_ref_known(v___x_563_, 1);
v_keys_x27_568_ = l_Array_eraseIdx___redArg(v_ks_558_, v_val_567_);
v_vals_x27_569_ = l_Array_eraseIdx___redArg(v_vs_559_, v_val_567_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_vals_x27_569_);
lean_ctor_set(v___x_561_, 0, v_keys_x27_568_);
v___x_571_ = v___x_561_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_keys_x27_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_vals_x27_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_495_ = stack[0].m_obj;
size_t v_x_496_ = stack[1].m_num;
lean_object* v_x_497_ = stack[2].m_obj;
lean_object* v_res_574_;
v_res_574_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_495_, v_x_496_, v_x_497_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
size_t v_x_621__boxed_578_; lean_object* v_res_579_; 
v_x_621__boxed_578_ = lean_unbox_usize(v_x_576_);
lean_dec(v_x_576_);
v_res_579_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_575_, v_x_621__boxed_578_, v_x_577_);
lean_dec_ref(v_x_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
uint64_t v___y_583_; lean_object* v___y_587_; lean_object* v_declName_590_; 
v_declName_590_ = lean_ctor_get(v_x_581_, 0);
v___y_587_ = v_declName_590_;
goto v___jp_586_;
v___jp_582_:
{
size_t v_h_584_; lean_object* v___x_585_; 
v_h_584_ = lean_uint64_to_usize(v___y_583_);
v___x_585_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_580_, v_h_584_, v_x_581_);
return v___x_585_;
}
v___jp_586_:
{
if (lean_obj_tag(v___y_587_) == 0)
{
uint64_t v___x_588_; 
v___x_588_ = 1723ULL;
v___y_583_ = v___x_588_;
goto v___jp_582_;
}
else
{
uint64_t v_hash_589_; 
v_hash_589_ = lean_ctor_get_uint64(v___y_587_, sizeof(void*)*2);
v___y_583_ = v_hash_589_;
goto v___jp_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_591_, v_x_592_);
lean_dec_ref(v_x_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
lean_object* v_ks_598_; lean_object* v_vs_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_628_; 
v_ks_598_ = lean_ctor_get(v_x_594_, 0);
v_vs_599_ = lean_ctor_get(v_x_594_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_628_ == 0)
{
v___x_601_ = v_x_594_;
v_isShared_602_ = v_isSharedCheck_628_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_vs_599_);
lean_inc(v_ks_598_);
lean_dec(v_x_594_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_628_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_array_get_size(v_ks_598_);
v___x_619_ = lean_nat_dec_lt(v_x_595_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_601_);
lean_dec(v_x_595_);
v___x_620_ = lean_array_push(v_ks_598_, v_x_596_);
v___x_621_ = lean_array_push(v_vs_599_, v_x_597_);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v_k_x27_623_; lean_object* v___y_625_; lean_object* v_declName_627_; 
v_k_x27_623_ = lean_array_fget_borrowed(v_ks_598_, v_x_595_);
v_declName_627_ = lean_ctor_get(v_x_596_, 0);
lean_inc(v_declName_627_);
v___y_625_ = v_declName_627_;
goto v___jp_624_;
v___jp_624_:
{
lean_object* v_declName_626_; 
v_declName_626_ = lean_ctor_get(v_k_x27_623_, 0);
lean_inc(v_declName_626_);
v___y_604_ = v___y_625_;
v___y_605_ = v_declName_626_;
goto v___jp_603_;
}
}
v___jp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_name_eq(v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec(v___y_604_);
if (v___x_606_ == 0)
{
lean_object* v___x_608_; 
if (v_isShared_602_ == 0)
{
v___x_608_ = v___x_601_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_ks_598_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_vs_599_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_x_595_, v___x_609_);
lean_dec(v_x_595_);
v_x_594_ = v___x_608_;
v_x_595_ = v___x_610_;
goto _start;
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_613_ = lean_array_fset(v_ks_598_, v_x_595_, v_x_596_);
v___x_614_ = lean_array_fset(v_vs_599_, v_x_595_, v_x_597_);
lean_dec(v_x_595_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v___x_614_);
lean_ctor_set(v___x_601_, 0, v___x_613_);
v___x_616_ = v___x_601_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object* v_n_629_, lean_object* v_k_630_, lean_object* v_v_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_n_629_, v___x_632_, v_k_630_, v_v_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_634_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object* v_x_635_, size_t v_x_636_, size_t v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v_es_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v_j_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_es_640_ = lean_ctor_get(v_x_635_, 0);
v___x_641_ = ((size_t)31ULL);
v___x_642_ = lean_usize_land(v_x_636_, v___x_641_);
v_j_643_ = lean_usize_to_nat(v___x_642_);
v___x_644_ = lean_array_get_size(v_es_640_);
v___x_645_ = lean_nat_dec_lt(v_j_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v_j_643_);
lean_dec(v_x_639_);
lean_dec_ref(v_x_638_);
return v_x_635_;
}
else
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_691_; 
lean_inc_ref(v_es_640_);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v_x_635_, 0);
lean_dec(v_unused_692_);
v___x_647_ = v_x_635_;
v_isShared_648_ = v_isSharedCheck_691_;
goto v_resetjp_646_;
}
else
{
lean_dec(v_x_635_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_691_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_v_649_; lean_object* v___x_650_; lean_object* v_xs_x27_651_; lean_object* v___y_653_; 
v_v_649_ = lean_array_fget(v_es_640_, v_j_643_);
v___x_650_ = lean_box(0);
v_xs_x27_651_ = lean_array_fset(v_es_640_, v_j_643_, v___x_650_);
switch(lean_obj_tag(v_v_649_))
{
case 0:
{
lean_object* v_key_658_; lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_676_; 
v_key_658_ = lean_ctor_get(v_v_649_, 0);
v_val_659_ = lean_ctor_get(v_v_649_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_v_649_);
if (v_isSharedCheck_676_ == 0)
{
v___x_661_ = v_v_649_;
v_isShared_662_ = v_isSharedCheck_676_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_inc(v_key_658_);
lean_dec(v_v_649_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_676_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_673_; lean_object* v_declName_675_; 
v_declName_675_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_declName_675_);
v___y_673_ = v_declName_675_;
goto v___jp_672_;
v___jp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_name_eq(v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_del_object(v___x_661_);
v___x_667_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_658_, v_val_659_, v_x_638_, v_x_639_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___y_653_ = v___x_668_;
goto v___jp_652_;
}
else
{
lean_object* v___x_670_; 
lean_dec(v_val_659_);
lean_dec(v_key_658_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_x_639_);
lean_ctor_set(v___x_661_, 0, v_x_638_);
v___x_670_ = v___x_661_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_x_638_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_x_639_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v___y_653_ = v___x_670_;
goto v___jp_652_;
}
}
}
v___jp_672_:
{
lean_object* v_declName_674_; 
v_declName_674_ = lean_ctor_get(v_key_658_, 0);
lean_inc(v_declName_674_);
v___y_664_ = v___y_673_;
v___y_665_ = v_declName_674_;
goto v___jp_663_;
}
}
}
case 1:
{
lean_object* v_node_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_689_; 
v_node_677_ = lean_ctor_get(v_v_649_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_v_649_);
if (v_isSharedCheck_689_ == 0)
{
v___x_679_ = v_v_649_;
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_node_677_);
lean_dec(v_v_649_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
size_t v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_681_ = ((size_t)5ULL);
v___x_682_ = lean_usize_shift_right(v_x_636_, v___x_681_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_x_637_, v___x_683_);
v___x_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_node_677_, v___x_682_, v___x_684_, v_x_638_, v_x_639_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_685_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_653_ = v___x_687_;
goto v___jp_652_;
}
}
}
default: 
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_x_638_);
lean_ctor_set(v___x_690_, 1, v_x_639_);
v___y_653_ = v___x_690_;
goto v___jp_652_;
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_array_fset(v_xs_x27_651_, v_j_643_, v___y_653_);
lean_dec(v_j_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_654_);
v___x_656_ = v___x_647_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_object* v_ks_693_; lean_object* v_vs_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_712_; 
v_ks_693_ = lean_ctor_get(v_x_635_, 0);
v_vs_694_ = lean_ctor_get(v_x_635_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_712_ == 0)
{
v___x_696_ = v_x_635_;
v_isShared_697_ = v_isSharedCheck_712_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_vs_694_);
lean_inc(v_ks_693_);
lean_dec(v_x_635_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_712_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_ks_693_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_vs_694_);
v___x_699_ = v_reuseFailAlloc_711_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v_newNode_700_; size_t v___x_701_; uint8_t v___x_702_; 
v_newNode_700_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v___x_699_, v_x_638_, v_x_639_);
v___x_701_ = ((size_t)7ULL);
v___x_702_ = lean_usize_dec_le(v___x_701_, v_x_637_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_700_);
v___x_704_ = lean_unsigned_to_nat(4u);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
lean_dec(v___x_703_);
if (v___x_705_ == 0)
{
lean_object* v_ks_706_; lean_object* v_vs_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_ks_706_ = lean_ctor_get(v_newNode_700_, 0);
lean_inc_ref(v_ks_706_);
v_vs_707_ = lean_ctor_get(v_newNode_700_, 1);
lean_inc_ref(v_vs_707_);
lean_dec_ref(v_newNode_700_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0);
v___x_710_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_x_637_, v_ks_706_, v_vs_707_, v___x_708_, v___x_709_);
lean_dec_ref(v_vs_707_);
lean_dec_ref(v_ks_706_);
return v___x_710_;
}
else
{
return v_newNode_700_;
}
}
else
{
return v_newNode_700_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_635_ = stack[0].m_obj;
size_t v_x_636_ = stack[1].m_num;
size_t v_x_637_ = stack[2].m_num;
lean_object* v_x_638_ = stack[3].m_obj;
lean_object* v_x_639_ = stack[4].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_635_, v_x_636_, v_x_637_, v_x_638_, v_x_639_);
stack->m_obj
 = v_res_713_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t v_depth_714_, lean_object* v_keys_715_, lean_object* v_vals_716_, lean_object* v_i_717_, lean_object* v_entries_718_){
_start:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_array_get_size(v_keys_715_);
v___x_720_ = lean_nat_dec_lt(v_i_717_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_i_717_);
return v_entries_718_;
}
else
{
lean_object* v_k_721_; lean_object* v_v_722_; uint64_t v___y_724_; lean_object* v___y_736_; lean_object* v_declName_739_; 
v_k_721_ = lean_array_fget_borrowed(v_keys_715_, v_i_717_);
v_v_722_ = lean_array_fget_borrowed(v_vals_716_, v_i_717_);
v_declName_739_ = lean_ctor_get(v_k_721_, 0);
lean_inc(v_declName_739_);
v___y_736_ = v_declName_739_;
goto v___jp_735_;
v___jp_723_:
{
size_t v_h_725_; size_t v___x_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v_h_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_h_725_ = lean_uint64_to_usize(v___y_724_);
v___x_726_ = ((size_t)5ULL);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_sub(v_depth_714_, v___x_728_);
v___x_730_ = lean_usize_mul(v___x_726_, v___x_729_);
v_h_731_ = lean_usize_shift_right(v_h_725_, v___x_730_);
v___x_732_ = lean_nat_add(v_i_717_, v___x_727_);
lean_dec(v_i_717_);
lean_inc(v_v_722_);
lean_inc(v_k_721_);
v___x_733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_entries_718_, v_h_731_, v_depth_714_, v_k_721_, v_v_722_);
v_i_717_ = v___x_732_;
v_entries_718_ = v___x_733_;
goto _start;
}
v___jp_735_:
{
if (lean_obj_tag(v___y_736_) == 0)
{
uint64_t v___x_737_; 
v___x_737_ = 1723ULL;
v___y_724_ = v___x_737_;
goto v___jp_723_;
}
else
{
uint64_t v_hash_738_; 
v_hash_738_ = lean_ctor_get_uint64(v___y_736_, sizeof(void*)*2);
lean_dec(v___y_736_);
v___y_724_ = v_hash_738_;
goto v___jp_723_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_714_ = stack[0].m_num;
lean_object* v_keys_715_ = stack[1].m_obj;
lean_object* v_vals_716_ = stack[2].m_obj;
lean_object* v_i_717_ = stack[3].m_obj;
lean_object* v_entries_718_ = stack[4].m_obj;
lean_object* v_res_740_;
v_res_740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_714_, v_keys_715_, v_vals_716_, v_i_717_, v_entries_718_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_741_, lean_object* v_keys_742_, lean_object* v_vals_743_, lean_object* v_i_744_, lean_object* v_entries_745_){
_start:
{
size_t v_depth_boxed_746_; lean_object* v_res_747_; 
v_depth_boxed_746_ = lean_unbox_usize(v_depth_741_);
lean_dec(v_depth_741_);
v_res_747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_boxed_746_, v_keys_742_, v_vals_743_, v_i_744_, v_entries_745_);
lean_dec_ref(v_vals_743_);
lean_dec_ref(v_keys_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
size_t v_x_1029__boxed_753_; size_t v_x_1030__boxed_754_; lean_object* v_res_755_; 
v_x_1029__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_x_1030__boxed_754_ = lean_unbox_usize(v_x_750_);
lean_dec(v_x_750_);
v_res_755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_748_, v_x_1029__boxed_753_, v_x_1030__boxed_754_, v_x_751_, v_x_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint64_t v___y_760_; lean_object* v___y_765_; lean_object* v_declName_768_; 
v_declName_768_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_declName_768_);
v___y_765_ = v_declName_768_;
goto v___jp_764_;
v___jp_759_:
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_uint64_to_usize(v___y_760_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_756_, v___x_761_, v___x_762_, v_x_757_, v_x_758_);
return v___x_763_;
}
v___jp_764_:
{
if (lean_obj_tag(v___y_765_) == 0)
{
uint64_t v___x_766_; 
v___x_766_ = 1723ULL;
v___y_760_ = v___x_766_;
goto v___jp_759_;
}
else
{
uint64_t v_hash_767_; 
v_hash_767_ = lean_ctor_get_uint64(v___y_765_, sizeof(void*)*2);
lean_dec(v___y_765_);
v___y_760_ = v_hash_767_;
goto v___jp_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object* v_s_769_, lean_object* v_origin_770_){
_start:
{
lean_object* v_smap_771_; lean_object* v_origins_772_; lean_object* v_erased_773_; lean_object* v_omap_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_784_; 
v_smap_771_ = lean_ctor_get(v_s_769_, 0);
v_origins_772_ = lean_ctor_get(v_s_769_, 1);
v_erased_773_ = lean_ctor_get(v_s_769_, 2);
v_omap_774_ = lean_ctor_get(v_s_769_, 3);
v_isSharedCheck_784_ = !lean_is_exclusive(v_s_769_);
if (v_isSharedCheck_784_ == 0)
{
v___x_776_ = v_s_769_;
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_omap_774_);
lean_inc(v_erased_773_);
lean_inc(v_origins_772_);
lean_inc(v_smap_771_);
lean_dec(v_s_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_778_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_origins_772_, v_origin_770_);
v___x_779_ = lean_box(0);
v___x_780_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_erased_773_, v_origin_770_, v___x_779_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_780_);
lean_ctor_set(v___x_776_, 1, v___x_778_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_smap_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_omap_774_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object* v_00_u03b1_785_, lean_object* v_s_786_, lean_object* v_origin_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_786_, v_origin_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(v_00_u03b2_793_, v_x_794_, v_x_795_);
lean_dec_ref(v_x_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_803_ = stack[1].m_obj;
size_t v_x_804_ = stack[2].m_num;
lean_object* v_x_805_ = stack[3].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_box(0), v_x_803_, v_x_804_, v_x_805_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
size_t v_x_1402__boxed_812_; lean_object* v_res_813_; 
v_x_1402__boxed_812_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_res_813_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(v_00_u03b2_808_, v_x_809_, v_x_1402__boxed_812_, v_x_811_);
lean_dec_ref(v_x_811_);
return v_res_813_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, size_t v_x_816_, size_t v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_815_, v_x_816_, v_x_817_, v_x_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_815_ = stack[1].m_obj;
size_t v_x_816_ = stack[2].m_num;
size_t v_x_817_ = stack[3].m_num;
lean_object* v_x_818_ = stack[4].m_obj;
lean_object* v_x_819_ = stack[5].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_box(0), v_x_815_, v_x_816_, v_x_817_, v_x_818_, v_x_819_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_1420__boxed_828_; size_t v_x_1421__boxed_829_; lean_object* v_res_830_; 
v_x_1420__boxed_828_ = lean_unbox_usize(v_x_824_);
lean_dec(v_x_824_);
v_x_1421__boxed_829_ = lean_unbox_usize(v_x_825_);
lean_dec(v_x_825_);
v_res_830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(v_00_u03b2_822_, v_x_823_, v_x_1420__boxed_828_, v_x_1421__boxed_829_, v_x_826_, v_x_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_831_, lean_object* v_n_832_, lean_object* v_k_833_, lean_object* v_v_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v_n_832_, v_k_833_, v_v_834_);
return v___x_835_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_836_, size_t v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_837_, v_keys_838_, v_vals_839_, v_i_841_, v_entries_842_);
return v___x_843_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_837_ = stack[1].m_num;
lean_object* v_keys_838_ = stack[2].m_obj;
lean_object* v_vals_839_ = stack[3].m_obj;
lean_object* v_i_841_ = stack[5].m_obj;
lean_object* v_entries_842_ = stack[6].m_obj;
lean_object* v_res_844_;
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_box(0), v_depth_837_, v_keys_838_, v_vals_839_, lean_box(0), v_i_841_, v_entries_842_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_845_, lean_object* v_depth_846_, lean_object* v_keys_847_, lean_object* v_vals_848_, lean_object* v_heq_849_, lean_object* v_i_850_, lean_object* v_entries_851_){
_start:
{
size_t v_depth_boxed_852_; lean_object* v_res_853_; 
v_depth_boxed_852_ = lean_unbox_usize(v_depth_846_);
lean_dec(v_depth_846_);
v_res_853_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(v_00_u03b2_845_, v_depth_boxed_852_, v_keys_847_, v_vals_848_, v_heq_849_, v_i_850_, v_entries_851_);
lean_dec_ref(v_vals_848_);
lean_dec_ref(v_keys_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_x_855_, v_x_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object* v_s_860_, lean_object* v_origin_861_){
_start:
{
lean_object* v_erased_862_; uint8_t v___x_863_; 
v_erased_862_ = lean_ctor_get(v_s_860_, 2);
v___x_863_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_862_, v_origin_861_);
return v___x_863_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_isErased___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_860_ = stack[0].m_obj;
lean_object* v_origin_861_ = stack[1].m_obj;
uint8_t v_res_864_;
v_res_864_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_860_, v_origin_861_);
stack->m_num = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object* v_s_865_, lean_object* v_origin_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_865_, v_origin_866_);
lean_dec_ref(v_origin_866_);
lean_dec_ref(v_s_865_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object* v_00_u03b1_869_, lean_object* v_s_870_, lean_object* v_origin_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_870_, v_origin_871_);
return v___x_872_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_isErased_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_870_ = stack[1].m_obj;
lean_object* v_origin_871_ = stack[2].m_obj;
uint8_t v_res_873_;
v_res_873_ = l_Lean_Meta_Grind_Theorems_isErased(lean_box(0), v_s_870_, v_origin_871_);
stack->m_num = v_res_873_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object* v_00_u03b1_874_, lean_object* v_s_875_, lean_object* v_origin_876_){
_start:
{
uint8_t v_res_877_; lean_object* v_r_878_; 
v_res_877_ = l_Lean_Meta_Grind_Theorems_isErased(v_00_u03b1_874_, v_s_875_, v_origin_876_);
lean_dec_ref(v_origin_876_);
lean_dec_ref(v_s_875_);
v_r_878_ = lean_box(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object* v_s_879_, lean_object* v_sym_880_){
_start:
{
lean_object* v_smap_881_; lean_object* v_origins_882_; lean_object* v_erased_883_; lean_object* v_omap_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_905_; 
v_smap_881_ = lean_ctor_get(v_s_879_, 0);
v_origins_882_ = lean_ctor_get(v_s_879_, 1);
v_erased_883_ = lean_ctor_get(v_s_879_, 2);
v_omap_884_ = lean_ctor_get(v_s_879_, 3);
v_isSharedCheck_905_ = !lean_is_exclusive(v_s_879_);
if (v_isSharedCheck_905_ == 0)
{
v___x_886_ = v_s_879_;
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_omap_884_);
lean_inc(v_erased_883_);
lean_inc(v_origins_882_);
lean_inc(v_smap_881_);
lean_dec(v_s_879_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_889_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_880_);
v___x_890_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_888_, v___x_889_, v_smap_881_, v_sym_880_);
if (lean_obj_tag(v___x_890_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_val_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_903_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_PersistentHashMap_erase___redArg(v___x_888_, v___x_889_, v_smap_881_, v_sym_880_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_895_);
v___x_897_ = v___x_886_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_origins_882_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_erased_883_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_omap_884_);
v___x_897_ = v_reuseFailAlloc_902_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_val_891_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_898_);
v___x_900_ = v___x_893_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___x_904_; 
lean_dec(v___x_890_);
lean_del_object(v___x_886_);
lean_dec_ref(v_omap_884_);
lean_dec_ref(v_erased_883_);
lean_dec_ref(v_origins_882_);
lean_dec_ref(v_smap_881_);
lean_dec(v_sym_880_);
v___x_904_ = lean_box(0);
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object* v_00_u03b1_906_, lean_object* v_s_907_, lean_object* v_sym_908_){
_start:
{
lean_object* v_smap_909_; lean_object* v_origins_910_; lean_object* v_erased_911_; lean_object* v_omap_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_933_; 
v_smap_909_ = lean_ctor_get(v_s_907_, 0);
v_origins_910_ = lean_ctor_get(v_s_907_, 1);
v_erased_911_ = lean_ctor_get(v_s_907_, 2);
v_omap_912_ = lean_ctor_get(v_s_907_, 3);
v_isSharedCheck_933_ = !lean_is_exclusive(v_s_907_);
if (v_isSharedCheck_933_ == 0)
{
v___x_914_ = v_s_907_;
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_omap_912_);
lean_inc(v_erased_911_);
lean_inc(v_origins_910_);
lean_inc(v_smap_909_);
lean_dec(v_s_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_917_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_908_);
v___x_918_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_916_, v___x_917_, v_smap_909_, v_sym_908_);
if (lean_obj_tag(v___x_918_) == 1)
{
lean_object* v_val_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_931_; 
v_val_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_931_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_val_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_931_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = l_Lean_PersistentHashMap_erase___redArg(v___x_916_, v___x_917_, v_smap_909_, v_sym_908_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_923_);
v___x_925_ = v___x_914_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_origins_910_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_erased_911_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_omap_912_);
v___x_925_ = v_reuseFailAlloc_930_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_val_919_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_926_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
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
else
{
lean_object* v___x_932_; 
lean_dec(v___x_918_);
lean_del_object(v___x_914_);
lean_dec_ref(v_omap_912_);
lean_dec_ref(v_erased_911_);
lean_dec_ref(v_origins_910_);
lean_dec_ref(v_smap_909_);
lean_dec(v_sym_908_);
v___x_932_ = lean_box(0);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_i_936_, lean_object* v_k_937_){
_start:
{
lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = lean_array_get_size(v_keys_934_);
v___x_948_ = lean_nat_dec_lt(v_i_936_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v_i_936_);
v___x_949_ = lean_box(0);
return v___x_949_;
}
else
{
lean_object* v_k_x27_950_; lean_object* v___y_952_; lean_object* v_declName_954_; 
v_k_x27_950_ = lean_array_fget_borrowed(v_keys_934_, v_i_936_);
v_declName_954_ = lean_ctor_get(v_k_937_, 0);
v___y_952_ = v_declName_954_;
goto v___jp_951_;
v___jp_951_:
{
lean_object* v_declName_953_; 
v_declName_953_ = lean_ctor_get(v_k_x27_950_, 0);
v___y_939_ = v___y_952_;
v___y_940_ = v_declName_953_;
goto v___jp_938_;
}
}
v___jp_938_:
{
uint8_t v___x_941_; 
v___x_941_ = lean_name_eq(v___y_939_, v___y_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_i_936_, v___x_942_);
lean_dec(v_i_936_);
v_i_936_ = v___x_943_;
goto _start;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_array_fget_borrowed(v_vals_935_, v_i_936_);
lean_dec(v_i_936_);
lean_inc(v___x_945_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_i_957_, lean_object* v_k_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_955_, v_vals_956_, v_i_957_, v_k_958_);
lean_dec_ref(v_k_958_);
lean_dec_ref(v_vals_956_);
lean_dec_ref(v_keys_955_);
return v_res_959_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object* v_x_960_, size_t v_x_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v_es_963_; lean_object* v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v_j_967_; lean_object* v___x_968_; 
v_es_963_ = lean_ctor_get(v_x_960_, 0);
v___x_964_ = lean_box(2);
v___x_965_ = ((size_t)31ULL);
v___x_966_ = lean_usize_land(v_x_961_, v___x_965_);
v_j_967_ = lean_usize_to_nat(v___x_966_);
v___x_968_ = lean_array_get_borrowed(v___x_964_, v_es_963_, v_j_967_);
lean_dec(v_j_967_);
switch(lean_obj_tag(v___x_968_))
{
case 0:
{
lean_object* v_key_969_; lean_object* v_val_970_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_978_; lean_object* v_declName_980_; 
v_key_969_ = lean_ctor_get(v___x_968_, 0);
v_val_970_ = lean_ctor_get(v___x_968_, 1);
v_declName_980_ = lean_ctor_get(v_x_962_, 0);
v___y_978_ = v_declName_980_;
goto v___jp_977_;
v___jp_971_:
{
uint8_t v___x_974_; 
v___x_974_ = lean_name_eq(v___y_972_, v___y_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_box(0);
return v___x_975_;
}
else
{
lean_object* v___x_976_; 
lean_inc(v_val_970_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_val_970_);
return v___x_976_;
}
}
v___jp_977_:
{
lean_object* v_declName_979_; 
v_declName_979_ = lean_ctor_get(v_key_969_, 0);
v___y_972_ = v___y_978_;
v___y_973_ = v_declName_979_;
goto v___jp_971_;
}
}
case 1:
{
lean_object* v_node_981_; size_t v___x_982_; size_t v___x_983_; 
v_node_981_ = lean_ctor_get(v___x_968_, 0);
v___x_982_ = ((size_t)5ULL);
v___x_983_ = lean_usize_shift_right(v_x_961_, v___x_982_);
v_x_960_ = v_node_981_;
v_x_961_ = v___x_983_;
goto _start;
}
default: 
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
}
}
else
{
lean_object* v_ks_986_; lean_object* v_vs_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_ks_986_ = lean_ctor_get(v_x_960_, 0);
v_vs_987_ = lean_ctor_get(v_x_960_, 1);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_ks_986_, v_vs_987_, v___x_988_, v_x_962_);
return v___x_989_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_960_ = stack[0].m_obj;
size_t v_x_961_ = stack[1].m_num;
lean_object* v_x_962_ = stack[2].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_960_, v_x_961_, v_x_962_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_241__boxed_994_; lean_object* v_res_995_; 
v_x_241__boxed_994_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_995_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_991_, v_x_241__boxed_994_, v_x_993_);
lean_dec_ref(v_x_993_);
lean_dec_ref(v_x_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
uint64_t v___y_999_; lean_object* v___y_1003_; lean_object* v_declName_1006_; 
v_declName_1006_ = lean_ctor_get(v_x_997_, 0);
v___y_1003_ = v_declName_1006_;
goto v___jp_1002_;
v___jp_998_:
{
size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_uint64_to_usize(v___y_999_);
v___x_1001_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_996_, v___x_1000_, v_x_997_);
return v___x_1001_;
}
v___jp_1002_:
{
if (lean_obj_tag(v___y_1003_) == 0)
{
uint64_t v___x_1004_; 
v___x_1004_ = 1723ULL;
v___y_999_ = v___x_1004_;
goto v___jp_998_;
}
else
{
uint64_t v_hash_1005_; 
v_hash_1005_ = lean_ctor_get_uint64(v___y_1003_, sizeof(void*)*2);
v___y_999_ = v_hash_1005_;
goto v___jp_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_1007_, v_x_1008_);
lean_dec_ref(v_x_1008_);
lean_dec_ref(v_x_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object* v_s_1010_, lean_object* v_origin_1011_){
_start:
{
lean_object* v_omap_1012_; lean_object* v___x_1013_; 
v_omap_1012_ = lean_ctor_get(v_s_1010_, 3);
v___x_1013_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_omap_1012_, v_origin_1011_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1013_, 1);
return v_val_1014_;
}
else
{
lean_object* v___x_1015_; 
lean_dec(v___x_1013_);
v___x_1015_ = lean_box(0);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object* v_s_1016_, lean_object* v_origin_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_1016_, v_origin_1017_);
lean_dec_ref(v_origin_1017_);
lean_dec_ref(v_s_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object* v_00_u03b1_1019_, lean_object* v_s_1020_, lean_object* v_origin_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_1020_, v_origin_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_s_1024_, lean_object* v_origin_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Grind_Theorems_find(v_00_u03b1_1023_, v_s_1024_, v_origin_1025_);
lean_dec_ref(v_origin_1025_);
lean_dec_ref(v_s_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object* v_00_u03b2_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(v_00_u03b2_1031_, v_x_1032_, v_x_1033_);
lean_dec_ref(v_x_1033_);
lean_dec_ref(v_x_1032_);
return v_res_1034_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, size_t v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_1036_, v_x_1037_, v_x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1036_ = stack[1].m_obj;
size_t v_x_1037_ = stack[2].m_num;
lean_object* v_x_1038_ = stack[3].m_obj;
lean_object* v_res_1040_;
v_res_1040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_box(0), v_x_1036_, v_x_1037_, v_x_1038_);
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
size_t v_x_405__boxed_1045_; lean_object* v_res_1046_; 
v_x_405__boxed_1045_ = lean_unbox_usize(v_x_1043_);
lean_dec(v_x_1043_);
v_res_1046_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(v_00_u03b2_1041_, v_x_1042_, v_x_405__boxed_1045_, v_x_1044_);
lean_dec_ref(v_x_1044_);
lean_dec_ref(v_x_1042_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1047_, lean_object* v_keys_1048_, lean_object* v_vals_1049_, lean_object* v_heq_1050_, lean_object* v_i_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_1048_, v_vals_1049_, v_i_1051_, v_k_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1054_, lean_object* v_keys_1055_, lean_object* v_vals_1056_, lean_object* v_heq_1057_, lean_object* v_i_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(v_00_u03b2_1054_, v_keys_1055_, v_vals_1056_, v_heq_1057_, v_i_1058_, v_k_1059_);
lean_dec_ref(v_k_1059_);
lean_dec_ref(v_vals_1056_);
lean_dec_ref(v_keys_1055_);
return v_res_1060_;
}
}
lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1061_ = stack[0].m_obj;
lean_object* v___y_1062_ = stack[1].m_obj;
lean_object* v___y_1063_ = stack[2].m_obj;
lean_object* v___y_1064_ = stack[3].m_obj;
lean_object* v___y_1065_ = stack[4].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object* v_x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(v_x_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_x_1069_);
return v_res_1075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_instMonadEIO___redArg();
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0);
v___x_1078_ = l_StateRefT_x27_instMonad___redArg(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___f_1084_; 
v___x_1083_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1084_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1084_, 0, v___x_1083_);
return v___f_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___f_1086_; 
v___x_1085_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1086_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1086_, 0, v___x_1085_);
return v___f_1086_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8(void){
_start:
{
lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; 
v___f_1087_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7);
v___f_1088_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___f_1088_);
lean_ctor_set(v___x_1089_, 1, v___f_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___f_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1091_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1091_, 0, v___x_1090_);
return v___f_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___f_1093_; 
v___x_1092_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1093_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1093_, 0, v___x_1092_);
return v___f_1093_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11(void){
_start:
{
lean_object* v___f_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1094_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10);
v___f_1095_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___f_1095_);
lean_ctor_set(v___x_1096_, 1, v___f_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1101_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15));
v___x_1103_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14));
v___x_1104_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1103_, v___x_1102_, v___x_1101_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___x_1105_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16);
v___f_1106_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13));
v___f_1107_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12));
v___x_1108_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1107_, v___f_1106_, v___x_1105_);
return v___x_1108_;
}
}
lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object* v_inst_1110_, lean_object* v_thm_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v_toApplicative_1118_; lean_object* v_toFunctor_1119_; lean_object* v_toSeq_1120_; lean_object* v_toSeqLeft_1121_; lean_object* v_toSeqRight_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_toApplicative_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1226_; 
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1);
v_toApplicative_1118_ = lean_ctor_get(v___x_1117_, 0);
v_toFunctor_1119_ = lean_ctor_get(v_toApplicative_1118_, 0);
v_toSeq_1120_ = lean_ctor_get(v_toApplicative_1118_, 2);
v_toSeqLeft_1121_ = lean_ctor_get(v_toApplicative_1118_, 3);
v_toSeqRight_1122_ = lean_ctor_get(v_toApplicative_1118_, 4);
v___f_1123_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2));
v___f_1124_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1119_, 2);
v___f_1125_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1125_, 0, v_toFunctor_1119_);
v___f_1126_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1126_, 0, v_toFunctor_1119_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___f_1125_);
lean_ctor_set(v___x_1127_, 1, v___f_1126_);
lean_inc(v_toSeqRight_1122_);
v___f_1128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1128_, 0, v_toSeqRight_1122_);
lean_inc(v_toSeqLeft_1121_);
v___f_1129_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1129_, 0, v_toSeqLeft_1121_);
lean_inc(v_toSeq_1120_);
v___f_1130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1130_, 0, v_toSeq_1120_);
v___x_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1127_);
lean_ctor_set(v___x_1131_, 1, v___f_1123_);
lean_ctor_set(v___x_1131_, 2, v___f_1130_);
lean_ctor_set(v___x_1131_, 3, v___f_1129_);
lean_ctor_set(v___x_1131_, 4, v___f_1128_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___f_1124_);
v___x_1133_ = l_StateRefT_x27_instMonad___redArg(v___x_1132_);
v_toApplicative_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1133_, 1);
lean_dec(v_unused_1227_);
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1226_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_toApplicative_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1226_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_toFunctor_1138_; lean_object* v_toSeq_1139_; lean_object* v_toSeqLeft_1140_; lean_object* v_toSeqRight_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1224_; 
v_toFunctor_1138_ = lean_ctor_get(v_toApplicative_1134_, 0);
v_toSeq_1139_ = lean_ctor_get(v_toApplicative_1134_, 2);
v_toSeqLeft_1140_ = lean_ctor_get(v_toApplicative_1134_, 3);
v_toSeqRight_1141_ = lean_ctor_get(v_toApplicative_1134_, 4);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_toApplicative_1134_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_toApplicative_1134_, 1);
lean_dec(v_unused_1225_);
v___x_1143_ = v_toApplicative_1134_;
v_isShared_1144_ = v_isSharedCheck_1224_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_toSeqRight_1141_);
lean_inc(v_toSeqLeft_1140_);
lean_inc(v_toSeq_1139_);
lean_inc(v_toFunctor_1138_);
lean_dec(v_toApplicative_1134_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1224_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___f_1145_; lean_object* v___f_1146_; lean_object* v___f_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1154_; 
v___f_1145_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
v___f_1146_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
lean_inc_ref(v_toFunctor_1138_);
v___f_1147_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1147_, 0, v_toFunctor_1138_);
v___f_1148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1148_, 0, v_toFunctor_1138_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___f_1147_);
lean_ctor_set(v___x_1149_, 1, v___f_1148_);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1150_, 0, v_toSeqRight_1141_);
v___f_1151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1151_, 0, v_toSeqLeft_1140_);
v___f_1152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1152_, 0, v_toSeq_1139_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 4, v___f_1150_);
lean_ctor_set(v___x_1143_, 3, v___f_1151_);
lean_ctor_set(v___x_1143_, 2, v___f_1152_);
lean_ctor_set(v___x_1143_, 1, v___f_1145_);
lean_ctor_set(v___x_1143_, 0, v___x_1149_);
v___x_1154_ = v___x_1143_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___f_1145_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v___f_1152_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v___f_1151_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v___f_1150_);
v___x_1154_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___f_1146_);
lean_ctor_set(v___x_1136_, 0, v___x_1154_);
v___x_1156_ = v___x_1136_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___f_1146_);
v___x_1156_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_toMonadRef_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_getProof_1164_; lean_object* v_getLevelParams_1165_; lean_object* v___f_1166_; lean_object* v_proof_1167_; lean_object* v_us_1168_; uint8_t v___y_1170_; uint8_t v___x_1218_; 
v___x_1157_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_1158_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11);
v___x_1159_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17);
v_toMonadRef_1160_ = lean_ctor_get(v___x_1159_, 0);
v___x_1161_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_1156_);
v___x_1162_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1161_, v___x_1156_);
lean_inc_ref(v_toMonadRef_1160_);
v___x_1163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1158_);
lean_ctor_set(v___x_1163_, 1, v_toMonadRef_1160_);
lean_ctor_set(v___x_1163_, 2, v___x_1162_);
v_getProof_1164_ = lean_ctor_get(v_inst_1110_, 3);
lean_inc_ref(v_getProof_1164_);
v_getLevelParams_1165_ = lean_ctor_get(v_inst_1110_, 4);
lean_inc_ref(v_getLevelParams_1165_);
lean_dec_ref(v_inst_1110_);
v___f_1166_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18));
lean_inc(v_thm_1111_);
v_proof_1167_ = lean_apply_1(v_getProof_1164_, v_thm_1111_);
v_us_1168_ = lean_apply_1(v_getLevelParams_1165_, v_thm_1111_);
v___x_1218_ = l_Lean_Expr_isConst(v_proof_1167_);
if (v___x_1218_ == 0)
{
v___y_1170_ = v___x_1218_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1219_ = lean_array_get_size(v_us_1168_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_nat_dec_eq(v___x_1219_, v___x_1220_);
v___y_1170_ = v___x_1221_;
goto v___jp_1169_;
}
v___jp_1169_:
{
if (v___y_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
lean_dec_ref_known(v___x_1163_, 3);
v___x_1171_ = lean_array_get_size(v_us_1168_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_nat_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_639__overap_1176_; lean_object* v___x_1177_; 
v_sz_1174_ = lean_array_size(v_us_1168_);
v___x_1175_ = ((size_t)0ULL);
lean_inc_ref(v_us_1168_);
v___x_639__overap_1176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1156_, v___f_1166_, v_sz_1174_, v___x_1175_, v_us_1168_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
v___x_1177_ = lean_apply_5(v___x_639__overap_1176_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, lean_box(0));
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_Expr_instantiateLevelParamsArray(v_proof_1167_, v_us_1168_, v_a_1178_);
lean_dec_ref(v_proof_1167_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_us_1168_);
lean_dec_ref(v_proof_1167_);
v_a_1187_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1177_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1177_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v___x_1195_; 
lean_dec_ref(v_us_1168_);
lean_dec_ref(v___x_1156_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_proof_1167_);
return v___x_1195_;
}
}
else
{
lean_object* v_declName_1196_; lean_object* v___x_685__overap_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_us_1168_);
v_declName_1196_ = l_Lean_Expr_constName_x21(v_proof_1167_);
lean_inc(v_declName_1196_);
v___x_685__overap_1197_ = l_Lean_getConstVal___redArg(v___x_1156_, v___x_1157_, v___x_1163_, v_declName_1196_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
v___x_1198_ = lean_apply_5(v___x_685__overap_1197_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_levelParams_1203_; uint8_t v___x_1204_; 
v_levelParams_1203_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_levelParams_1203_);
lean_dec(v_a_1199_);
v___x_1204_ = l_List_isEmpty___redArg(v_levelParams_1203_);
lean_dec(v_levelParams_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_del_object(v___x_1201_);
lean_dec_ref(v_proof_1167_);
v___x_1205_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_1196_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1205_;
}
else
{
lean_object* v___x_1207_; 
lean_dec(v_declName_1196_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v_proof_1167_);
v___x_1207_ = v___x_1201_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_proof_1167_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_declName_1196_);
lean_dec_ref(v_proof_1167_);
v_a_1210_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1198_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1198_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1110_ = stack[0].m_obj;
lean_object* v_thm_1111_ = stack[1].m_obj;
lean_object* v_a_1112_ = stack[2].m_obj;
lean_object* v_a_1113_ = stack[3].m_obj;
lean_object* v_a_1114_ = stack[4].m_obj;
lean_object* v_a_1115_ = stack[5].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1110_, v_thm_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object* v_inst_1229_, lean_object* v_thm_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1229_, v_thm_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1236_;
}
}
lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object* v_00_u03b1_1237_, lean_object* v_inst_1238_, lean_object* v_thm_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1238_, v_thm_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getProofWithFreshMVarLevels_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1238_ = stack[1].m_obj;
lean_object* v_thm_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_a_1241_ = stack[4].m_obj;
lean_object* v_a_1242_ = stack[5].m_obj;
lean_object* v_a_1243_ = stack[6].m_obj;
lean_object* v_res_1246_;
v_res_1246_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_box(0), v_inst_1238_, v_thm_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_inst_1248_, lean_object* v_thm_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(v_00_u03b1_1247_, v_inst_1248_, v_thm_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1255_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object* v_msgData_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_env_1263_; uint8_t v___x_1264_; lean_object* v_env_1265_; lean_object* v___x_1266_; lean_object* v_toCold_1267_; lean_object* v_mctx_1268_; lean_object* v_lctx_1269_; lean_object* v_options_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1262_ = lean_st_ref_get(v___y_1260_);
v_env_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_env_1263_);
lean_dec(v___x_1262_);
v___x_1264_ = 0;
v_env_1265_ = l_Lean_Environment_setRecordingDeps(v_env_1263_, v___x_1264_);
v___x_1266_ = lean_st_ref_get(v___y_1258_);
v_toCold_1267_ = lean_ctor_get(v___y_1259_, 0);
v_mctx_1268_ = lean_ctor_get(v___x_1266_, 0);
lean_inc_ref(v_mctx_1268_);
lean_dec(v___x_1266_);
v_lctx_1269_ = lean_ctor_get(v___y_1257_, 2);
v_options_1270_ = lean_ctor_get(v_toCold_1267_, 2);
lean_inc_ref(v_options_1270_);
lean_inc_ref(v_lctx_1269_);
v___x_1271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1271_, 0, v_env_1265_);
lean_ctor_set(v___x_1271_, 1, v_mctx_1268_);
lean_ctor_set(v___x_1271_, 2, v_lctx_1269_);
lean_ctor_set(v___x_1271_, 3, v_options_1270_);
v___x_1272_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_msgData_1256_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1256_ = stack[0].m_obj;
lean_object* v___y_1257_ = stack[1].m_obj;
lean_object* v___y_1258_ = stack[2].m_obj;
lean_object* v___y_1259_ = stack[3].m_obj;
lean_object* v___y_1260_ = stack[4].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_msgData_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
v_ref_1288_ = lean_ctor_get(v___y_1285_, 2);
v___x_1289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_inc(v_ref_1288_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_ref_1288_);
lean_ctor_set(v___x_1294_, 1, v_a_1290_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1282_ = stack[0].m_obj;
lean_object* v___y_1283_ = stack[1].m_obj;
lean_object* v___y_1284_ = stack[2].m_obj;
lean_object* v___y_1285_ = stack[3].m_obj;
lean_object* v___y_1286_ = stack[4].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object* v_declName_1313_, lean_object* v_00_u03b1_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1320_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1321_ = 0;
v___x_1322_ = l_Lean_MessageData_ofConstName(v_declName_1313_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1320_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_1325_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1326_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1313_ = stack[0].m_obj;
lean_object* v___y_1315_ = stack[2].m_obj;
lean_object* v___y_1316_ = stack[3].m_obj;
lean_object* v___y_1317_ = stack[4].m_obj;
lean_object* v___y_1318_ = stack[5].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1313_, lean_box(0), v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object* v_declName_1328_, lean_object* v_00_u03b1_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1328_, v_00_u03b1_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1335_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object* v_s_1336_, uint8_t v___x_1337_, lean_object* v_as_1338_, size_t v_i_1339_, size_t v_stop_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_eq(v_i_1339_, v_stop_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = 1;
v___x_1343_ = lean_array_uget_borrowed(v_as_1338_, v_i_1339_);
lean_inc(v___x_1343_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
v___x_1345_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1336_, v___x_1344_);
lean_dec_ref_known(v___x_1344_, 1);
if (v___x_1345_ == 0)
{
return v___x_1342_;
}
else
{
if (v___x_1337_ == 0)
{
size_t v___x_1346_; size_t v___x_1347_; 
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1339_, v___x_1346_);
v_i_1339_ = v___x_1347_;
goto _start;
}
else
{
return v___x_1342_;
}
}
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = 0;
return v___x_1349_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1336_ = stack[0].m_obj;
uint8_t v___x_1337_ = stack[1].m_num;
lean_object* v_as_1338_ = stack[2].m_obj;
size_t v_i_1339_ = stack[3].m_num;
size_t v_stop_1340_ = stack[4].m_num;
uint8_t v_res_1350_;
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1336_, v___x_1337_, v_as_1338_, v_i_1339_, v_stop_1340_);
stack->m_num = v_res_1350_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object* v_s_1351_, lean_object* v___x_1352_, lean_object* v_as_1353_, lean_object* v_i_1354_, lean_object* v_stop_1355_){
_start:
{
uint8_t v___x_2964__boxed_1356_; size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; uint8_t v_res_1359_; lean_object* v_r_1360_; 
v___x_2964__boxed_1356_ = lean_unbox(v___x_1352_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1355_);
lean_dec(v_stop_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1351_, v___x_2964__boxed_1356_, v_as_1353_, v_i_boxed_1357_, v_stop_boxed_1358_);
lean_dec_ref(v_as_1353_);
lean_dec_ref(v_s_1351_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object* v_as_1361_, size_t v_i_1362_, size_t v_stop_1363_, lean_object* v_b_1364_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_usize_dec_eq(v_i_1362_, v_stop_1363_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; 
v___x_1366_ = lean_array_uget_borrowed(v_as_1361_, v_i_1362_);
lean_inc(v___x_1366_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
v___x_1368_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_b_1364_, v___x_1367_);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1362_, v___x_1369_);
v_i_1362_ = v___x_1370_;
v_b_1364_ = v___x_1368_;
goto _start;
}
else
{
return v_b_1364_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1361_ = stack[0].m_obj;
size_t v_i_1362_ = stack[1].m_num;
size_t v_stop_1363_ = stack[2].m_num;
lean_object* v_b_1364_ = stack[3].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1361_, v_i_1362_, v_stop_1363_, v_b_1364_);
stack->m_obj
 = v_res_1372_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_as_1373_, lean_object* v_i_1374_, lean_object* v_stop_1375_, lean_object* v_b_1376_){
_start:
{
size_t v_i_boxed_1377_; size_t v_stop_boxed_1378_; lean_object* v_res_1379_; 
v_i_boxed_1377_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_stop_boxed_1378_ = lean_unbox_usize(v_stop_1375_);
lean_dec(v_stop_1375_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1373_, v_i_boxed_1377_, v_stop_boxed_1378_, v_b_1376_);
lean_dec_ref(v_as_1373_);
return v_res_1379_;
}
}
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object* v_s_1380_, lean_object* v_declName_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1391_; lean_object* v_env_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_st_ref_get(v_a_1385_);
v_env_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_env_1392_);
lean_dec(v___x_1391_);
lean_inc(v_declName_1381_);
v___x_1393_ = l_Lean_wasOriginallyTheorem(v_env_1392_, v_declName_1381_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_inc(v_declName_1381_);
v___x_1394_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1439_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1439_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1439_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
if (lean_obj_tag(v_a_1395_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_val_1399_ = lean_ctor_get(v_a_1395_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v_a_1395_, 1);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v_val_1399_);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_declName_1381_);
goto v___jp_1400_;
}
else
{
if (v___x_1425_ == 0)
{
lean_dec(v_declName_1381_);
goto v___jp_1400_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1424_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1380_, v___x_1393_, v_val_1399_, v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_dec(v_declName_1381_);
goto v___jp_1400_;
}
else
{
lean_object* v___x_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_val_1399_);
lean_del_object(v___x_1397_);
lean_dec_ref(v_s_1380_);
v___x_1429_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1381_, lean_box(0), v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
v___jp_1400_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_array_get_size(v_val_1399_);
v___x_1403_ = lean_nat_dec_lt(v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1405_; 
lean_dec(v_val_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_s_1380_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_s_1380_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1402_, v___x_1402_);
if (v___x_1407_ == 0)
{
if (v___x_1403_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_val_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_s_1380_);
v___x_1409_ = v___x_1397_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_s_1380_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1402_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1399_, v___x_1411_, v___x_1412_, v_s_1380_);
lean_dec(v_val_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1413_);
v___x_1415_ = v___x_1397_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1402_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1399_, v___x_1417_, v___x_1418_, v_s_1380_);
lean_dec(v_val_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1419_);
v___x_1421_ = v___x_1397_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v___x_1438_; 
lean_del_object(v___x_1397_);
lean_dec(v_a_1395_);
lean_dec_ref(v_s_1380_);
v___x_1438_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1381_, lean_box(0), v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_declName_1381_);
lean_dec_ref(v_s_1380_);
v_a_1440_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1394_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1394_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
lean_inc(v_declName_1381_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_declName_1381_);
v___x_1449_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1380_, v___x_1448_);
lean_dec_ref_known(v___x_1448_, 1);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_s_1380_);
v___x_1450_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1381_, lean_box(0), v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
goto v___jp_1387_;
}
}
v___jp_1387_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_declName_1381_);
v___x_1389_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_1380_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_eraseDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1380_ = stack[0].m_obj;
lean_object* v_declName_1381_ = stack[1].m_obj;
lean_object* v_a_1382_ = stack[2].m_obj;
lean_object* v_a_1383_ = stack[3].m_obj;
lean_object* v_a_1384_ = stack[4].m_obj;
lean_object* v_a_1385_ = stack[5].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1380_, v_declName_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object* v_s_1460_, lean_object* v_declName_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1460_, v_declName_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
return v_res_1467_;
}
}
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object* v_00_u03b1_1468_, lean_object* v_s_1469_, lean_object* v_declName_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1469_, v_declName_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_eraseDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1469_ = stack[1].m_obj;
lean_object* v_declName_1470_ = stack[2].m_obj;
lean_object* v_a_1471_ = stack[3].m_obj;
lean_object* v_a_1472_ = stack[4].m_obj;
lean_object* v_a_1473_ = stack[5].m_obj;
lean_object* v_a_1474_ = stack[6].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l_Lean_Meta_Grind_Theorems_eraseDecl(lean_box(0), v_s_1469_, v_declName_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_s_1479_, lean_object* v_declName_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_Grind_Theorems_eraseDecl(v_00_u03b1_1478_, v_s_1479_, v_declName_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1486_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object* v_00_u03b1_1487_, lean_object* v_msg_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1488_ = stack[1].m_obj;
lean_object* v___y_1489_ = stack[2].m_obj;
lean_object* v___y_1490_ = stack[3].m_obj;
lean_object* v___y_1491_ = stack[4].m_obj;
lean_object* v___y_1492_ = stack[5].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_box(0), v_msg_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(v_00_u03b1_1496_, v_msg_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1503_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object* v_00_u03b1_1504_, lean_object* v_as_1505_, size_t v_i_1506_, size_t v_stop_1507_, lean_object* v_b_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1505_, v_i_1506_, v_stop_1507_, v_b_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1505_ = stack[1].m_obj;
size_t v_i_1506_ = stack[2].m_num;
size_t v_stop_1507_ = stack[3].m_num;
lean_object* v_b_1508_ = stack[4].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_box(0), v_as_1505_, v_i_1506_, v_stop_1507_, v_b_1508_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_as_1512_, lean_object* v_i_1513_, lean_object* v_stop_1514_, lean_object* v_b_1515_){
_start:
{
size_t v_i_boxed_1516_; size_t v_stop_boxed_1517_; lean_object* v_res_1518_; 
v_i_boxed_1516_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_stop_boxed_1517_ = lean_unbox_usize(v_stop_1514_);
lean_dec(v_stop_1514_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(v_00_u03b1_1511_, v_as_1512_, v_i_boxed_1516_, v_stop_boxed_1517_, v_b_1515_);
lean_dec_ref(v_as_1512_);
return v_res_1518_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object* v_00_u03b1_1519_, lean_object* v_s_1520_, uint8_t v___x_1521_, lean_object* v_as_1522_, size_t v_i_1523_, size_t v_stop_1524_){
_start:
{
uint8_t v___x_1525_; 
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1520_, v___x_1521_, v_as_1522_, v_i_1523_, v_stop_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1520_ = stack[1].m_obj;
uint8_t v___x_1521_ = stack[2].m_num;
lean_object* v_as_1522_ = stack[3].m_obj;
size_t v_i_1523_ = stack[4].m_num;
size_t v_stop_1524_ = stack[5].m_num;
uint8_t v_res_1526_;
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_box(0), v_s_1520_, v___x_1521_, v_as_1522_, v_i_1523_, v_stop_1524_);
stack->m_num = v_res_1526_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_s_1528_, lean_object* v___x_1529_, lean_object* v_as_1530_, lean_object* v_i_1531_, lean_object* v_stop_1532_){
_start:
{
uint8_t v___x_3276__boxed_1533_; size_t v_i_boxed_1534_; size_t v_stop_boxed_1535_; uint8_t v_res_1536_; lean_object* v_r_1537_; 
v___x_3276__boxed_1533_ = lean_unbox(v___x_1529_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_stop_boxed_1535_ = lean_unbox_usize(v_stop_1532_);
lean_dec(v_stop_1532_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(v_00_u03b1_1527_, v_s_1528_, v___x_3276__boxed_1533_, v_as_1530_, v_i_boxed_1534_, v_stop_boxed_1535_);
lean_dec_ref(v_as_1530_);
lean_dec_ref(v_s_1528_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
if (lean_obj_tag(v_a_1538_) == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = l_List_reverse___redArg(v_a_1539_);
return v___x_1540_;
}
else
{
lean_object* v_head_1541_; lean_object* v_tail_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1551_; 
v_head_1541_ = lean_ctor_get(v_a_1538_, 0);
v_tail_1542_ = lean_ctor_get(v_a_1538_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_tail_1542_);
lean_inc(v_head_1541_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1546_; lean_object* v___x_1548_; 
v_fst_1546_ = lean_ctor_get(v_head_1541_, 0);
lean_inc(v_fst_1546_);
lean_dec(v_head_1541_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_a_1539_);
lean_ctor_set(v___x_1544_, 0, v_fst_1546_);
v___x_1548_ = v___x_1544_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_fst_1546_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1539_);
v___x_1548_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
v_a_1538_ = v_tail_1542_;
v_a_1539_ = v___x_1548_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_1552_, lean_object* v_k_1553_, lean_object* v_v_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_k_1553_);
lean_ctor_set(v___x_1555_, 1, v_v_1554_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_ps_1552_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1557_, lean_object* v_x1_1558_, lean_object* v_x2_1559_, lean_object* v_x3_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_apply_3(v_f_1557_, v_x1_1558_, v_x2_1559_, v_x3_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_f_1562_, lean_object* v_keys_1563_, lean_object* v_vals_1564_, lean_object* v_i_1565_, lean_object* v_acc_1566_){
_start:
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_array_get_size(v_keys_1563_);
v___x_1568_ = lean_nat_dec_lt(v_i_1565_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec(v_i_1565_);
lean_dec(v_f_1562_);
return v_acc_1566_;
}
else
{
lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_k_1569_ = lean_array_fget_borrowed(v_keys_1563_, v_i_1565_);
v_v_1570_ = lean_array_fget_borrowed(v_vals_1564_, v_i_1565_);
lean_inc(v_f_1562_);
lean_inc(v_v_1570_);
lean_inc(v_k_1569_);
v___x_1571_ = lean_apply_3(v_f_1562_, v_acc_1566_, v_k_1569_, v_v_1570_);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_i_1565_, v___x_1572_);
lean_dec(v_i_1565_);
v_i_1565_ = v___x_1573_;
v_acc_1566_ = v___x_1571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_f_1575_, lean_object* v_keys_1576_, lean_object* v_vals_1577_, lean_object* v_i_1578_, lean_object* v_acc_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1575_, v_keys_1576_, v_vals_1577_, v_i_1578_, v_acc_1579_);
lean_dec_ref(v_vals_1577_);
lean_dec_ref(v_keys_1576_);
return v_res_1580_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_f_1581_, lean_object* v_as_1582_, size_t v_i_1583_, size_t v_stop_1584_, lean_object* v_b_1585_){
_start:
{
lean_object* v___y_1587_; uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_eq(v_i_1583_, v_stop_1584_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_array_uget_borrowed(v_as_1582_, v_i_1583_);
switch(lean_obj_tag(v___x_1592_))
{
case 0:
{
lean_object* v_key_1593_; lean_object* v_val_1594_; lean_object* v___x_1595_; 
v_key_1593_ = lean_ctor_get(v___x_1592_, 0);
v_val_1594_ = lean_ctor_get(v___x_1592_, 1);
lean_inc(v_f_1581_);
lean_inc(v_val_1594_);
lean_inc(v_key_1593_);
v___x_1595_ = lean_apply_3(v_f_1581_, v_b_1585_, v_key_1593_, v_val_1594_);
v___y_1587_ = v___x_1595_;
goto v___jp_1586_;
}
case 1:
{
lean_object* v_node_1596_; lean_object* v___x_1597_; 
v_node_1596_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_f_1581_);
v___x_1597_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1581_, v_node_1596_, v_b_1585_);
v___y_1587_ = v___x_1597_;
goto v___jp_1586_;
}
default: 
{
v___y_1587_ = v_b_1585_;
goto v___jp_1586_;
}
}
}
else
{
lean_dec(v_f_1581_);
return v_b_1585_;
}
v___jp_1586_:
{
size_t v___x_1588_; size_t v___x_1589_; 
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1583_, v___x_1588_);
v_i_1583_ = v___x_1589_;
v_b_1585_ = v___y_1587_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1581_ = stack[0].m_obj;
lean_object* v_as_1582_ = stack[1].m_obj;
size_t v_i_1583_ = stack[2].m_num;
size_t v_stop_1584_ = stack[3].m_num;
lean_object* v_b_1585_ = stack[4].m_obj;
lean_object* v_res_1598_;
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1581_, v_as_1582_, v_i_1583_, v_stop_1584_, v_b_1585_);
stack->m_obj
 = v_res_1598_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_f_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
lean_object* v_es_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_es_1602_ = lean_ctor_get(v_x_1600_, 0);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_array_get_size(v_es_1602_);
v___x_1605_ = lean_nat_dec_lt(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_dec(v_f_1599_);
return v_x_1601_;
}
else
{
size_t v___x_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = lean_usize_of_nat(v___x_1604_);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1599_, v_es_1602_, v___x_1606_, v___x_1607_, v_x_1601_);
return v___x_1608_;
}
}
else
{
lean_object* v_ks_1609_; lean_object* v_vs_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_ks_1609_ = lean_ctor_get(v_x_1600_, 0);
v_vs_1610_ = lean_ctor_get(v_x_1600_, 1);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1599_, v_ks_1609_, v_vs_1610_, v___x_1611_, v_x_1601_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1613_, v_x_1614_, v_x_1615_);
lean_dec_ref(v_x_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_f_1617_, lean_object* v_as_1618_, lean_object* v_i_1619_, lean_object* v_stop_1620_, lean_object* v_b_1621_){
_start:
{
size_t v_i_boxed_1622_; size_t v_stop_boxed_1623_; lean_object* v_res_1624_; 
v_i_boxed_1622_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_stop_boxed_1623_ = lean_unbox_usize(v_stop_1620_);
lean_dec(v_stop_1620_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1617_, v_as_1618_, v_i_boxed_1622_, v_stop_boxed_1623_, v_b_1621_);
lean_dec_ref(v_as_1618_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1625_, lean_object* v_f_1626_, lean_object* v_init_1627_){
_start:
{
lean_object* v___f_1628_; lean_object* v___x_1629_; 
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1628_, 0, v_f_1626_);
v___x_1629_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v___f_1628_, v_map_1625_, v_init_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1630_, lean_object* v_f_1631_, lean_object* v_init_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1630_, v_f_1631_, v_init_1632_);
lean_dec_ref(v_map_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object* v_m_1635_){
_start:
{
lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___f_1636_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0));
v___x_1637_ = lean_box(0);
v___x_1638_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_m_1635_, v___f_1636_, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object* v_m_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1639_);
lean_dec_ref(v_m_1639_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object* v_s_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_s_1641_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(v___x_1642_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object* v_s_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_s_1645_);
lean_dec_ref(v_s_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object* v_s_1647_){
_start:
{
lean_object* v_origins_1648_; lean_object* v___x_1649_; 
v_origins_1648_ = lean_ctor_get(v_s_1647_, 1);
v___x_1649_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_origins_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object* v_s_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1650_);
lean_dec_ref(v_s_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object* v_00_u03b1_1652_, lean_object* v_s_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_s_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Meta_Grind_Theorems_getOrigins(v_00_u03b1_1655_, v_s_1656_);
lean_dec_ref(v_s_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object* v_00_u03b2_1658_, lean_object* v_m_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1661_, lean_object* v_m_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(v_00_u03b2_1661_, v_m_1662_);
lean_dec_ref(v_m_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1664_, lean_object* v_00_u03b2_1665_, lean_object* v_map_1666_, lean_object* v_f_1667_, lean_object* v_init_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1666_, v_f_1667_, v_init_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_map_1672_, lean_object* v_f_1673_, lean_object* v_init_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(v_00_u03c3_1670_, v_00_u03b2_1671_, v_map_1672_, v_f_1673_, v_init_1674_);
lean_dec_ref(v_map_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1676_, lean_object* v_f_1677_, lean_object* v_init_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1677_, v_map_1676_, v_init_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1680_, lean_object* v_f_1681_, lean_object* v_init_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(v_map_1680_, v_f_1681_, v_init_1682_);
lean_dec_ref(v_map_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1684_, lean_object* v_00_u03b2_1685_, lean_object* v_map_1686_, lean_object* v_f_1687_, lean_object* v_init_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1687_, v_map_1686_, v_init_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_map_1692_, lean_object* v_f_1693_, lean_object* v_init_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(v_00_u03c3_1690_, v_00_u03b2_1691_, v_map_1692_, v_f_1693_, v_init_1694_);
lean_dec_ref(v_map_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1696_, lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_f_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1699_, v_x_1700_, v_x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1703_, lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_f_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03c3_1703_, v_00_u03b1_1704_, v_00_u03b2_1705_, v_f_1706_, v_x_1707_, v_x_1708_);
lean_dec_ref(v_x_1707_);
return v_res_1709_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_00_u03c3_1712_, lean_object* v_f_1713_, lean_object* v_as_1714_, size_t v_i_1715_, size_t v_stop_1716_, lean_object* v_b_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1713_, v_as_1714_, v_i_1715_, v_stop_1716_, v_b_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1713_ = stack[3].m_obj;
lean_object* v_as_1714_ = stack[4].m_obj;
size_t v_i_1715_ = stack[5].m_num;
size_t v_stop_1716_ = stack[6].m_num;
lean_object* v_b_1717_ = stack[7].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_box(0), lean_box(0), lean_box(0), v_f_1713_, v_as_1714_, v_i_1715_, v_stop_1716_, v_b_1717_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_00_u03c3_1722_, lean_object* v_f_1723_, lean_object* v_as_1724_, lean_object* v_i_1725_, lean_object* v_stop_1726_, lean_object* v_b_1727_){
_start:
{
size_t v_i_boxed_1728_; size_t v_stop_boxed_1729_; lean_object* v_res_1730_; 
v_i_boxed_1728_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_stop_boxed_1729_ = lean_unbox_usize(v_stop_1726_);
lean_dec(v_stop_1726_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_00_u03b1_1720_, v_00_u03b2_1721_, v_00_u03c3_1722_, v_f_1723_, v_as_1724_, v_i_boxed_1728_, v_stop_boxed_1729_, v_b_1727_);
lean_dec_ref(v_as_1724_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03c3_1731_, lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_f_1734_, lean_object* v_keys_1735_, lean_object* v_vals_1736_, lean_object* v_heq_1737_, lean_object* v_i_1738_, lean_object* v_acc_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1734_, v_keys_1735_, v_vals_1736_, v_i_1738_, v_acc_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03c3_1741_, lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_f_1744_, lean_object* v_keys_1745_, lean_object* v_vals_1746_, lean_object* v_heq_1747_, lean_object* v_i_1748_, lean_object* v_acc_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03c3_1741_, v_00_u03b1_1742_, v_00_u03b2_1743_, v_f_1744_, v_keys_1745_, v_vals_1746_, v_heq_1747_, v_i_1748_, v_acc_1749_);
lean_dec_ref(v_vals_1746_);
lean_dec_ref(v_keys_1745_);
return v_res_1750_;
}
}
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg(){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__1);
return v___x_1752_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Theorems_mkEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1753_;
v_res_1753_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
stack->m_obj
 = v_res_1753_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg___boxed(lean_object* v___dummy_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v_res_1755_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object* v_00_u03b1_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1758_;
}
}
lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg(){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1760_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1761_;
v_res_1761_ = l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg();
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg___boxed(lean_object* v___dummy_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Meta_Grind_instEmptyCollectionTheorems___redArg();
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object* v_00_u03b1_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0, &l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0_once, _init_l_Lean_Meta_Grind_Theorems_mkEmpty___closed__0);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = l_List_reverse___redArg(v_a_1767_);
return v___x_1768_;
}
else
{
lean_object* v_head_1769_; lean_object* v_tail_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1779_; 
v_head_1769_ = lean_ctor_get(v_a_1766_, 0);
v_tail_1770_ = lean_ctor_get(v_a_1766_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1772_ = v_a_1766_;
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_tail_1770_);
lean_inc(v_head_1769_);
lean_dec(v_a_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = l_Lean_mkLevelParam(v_head_1769_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_a_1767_);
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_a_1767_);
v___x_1776_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
v_a_1766_ = v_tail_1770_;
v_a_1767_ = v___x_1776_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___redArg___closed__0);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
lean_ctor_set(v___x_1785_, 2, v___x_1784_);
lean_ctor_set(v___x_1785_, 3, v___x_1784_);
lean_ctor_set(v___x_1785_, 4, v___x_1783_);
lean_ctor_set(v___x_1785_, 5, v___x_1783_);
lean_ctor_set(v___x_1785_, 6, v___x_1783_);
lean_ctor_set(v___x_1785_, 7, v___x_1783_);
lean_ctor_set(v___x_1785_, 8, v___x_1783_);
lean_ctor_set(v___x_1785_, 9, v___x_1783_);
lean_ctor_set(v___x_1785_, 10, v___x_1783_);
lean_ctor_set(v___x_1785_, 11, v___x_1782_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_unsigned_to_nat(32u);
v___x_1787_ = lean_mk_empty_array_with_capacity(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = ((size_t)5ULL);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_unsigned_to_nat(32u);
v___x_1792_ = lean_mk_empty_array_with_capacity(v___x_1791_);
v___x_1793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1794_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___x_1792_);
lean_ctor_set(v___x_1794_, 2, v___x_1790_);
lean_ctor_set(v___x_1794_, 3, v___x_1790_);
lean_ctor_set_usize(v___x_1794_, 4, v___x_1789_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_box(1);
v___x_1796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v___x_1796_);
lean_ctor_set(v___x_1798_, 2, v___x_1795_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__23));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__25));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1832_, lean_object* v_declHint_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_env_1838_; uint8_t v___x_1839_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_st_ref_get(v___y_1834_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_env_1838_);
lean_dec(v___x_1837_);
v___x_1839_ = l_Lean_Name_isAnonymous(v_declHint_1833_);
if (v___x_1839_ == 0)
{
uint8_t v_isExporting_1840_; 
v_isExporting_1840_ = lean_ctor_get_uint8(v_env_1838_, sizeof(void*)*13);
if (v_isExporting_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v_env_1838_);
lean_dec(v_declHint_1833_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_msg_1832_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
lean_inc_ref(v_env_1838_);
v___x_1842_ = l_Lean_Environment_setExporting(v_env_1838_, v___x_1839_);
lean_inc(v_declHint_1833_);
lean_inc_ref(v___x_1842_);
v___x_1843_ = l_Lean_Environment_contains(v___x_1842_, v_declHint_1833_, v_isExporting_1840_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v___x_1842_);
lean_dec_ref(v_env_1838_);
lean_dec(v_declHint_1833_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_msg_1832_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_c_1850_; lean_object* v___x_1851_; 
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1847_ = l_Lean_Options_empty;
v___x_1848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1842_);
lean_ctor_set(v___x_1848_, 1, v___x_1845_);
lean_ctor_set(v___x_1848_, 2, v___x_1846_);
lean_ctor_set(v___x_1848_, 3, v___x_1847_);
lean_inc(v_declHint_1833_);
v___x_1849_ = l_Lean_MessageData_ofConstName(v_declHint_1833_, v___x_1839_);
v_c_1850_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1850_, 0, v___x_1848_);
lean_ctor_set(v_c_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1838_, v_declHint_1833_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v_env_1838_);
lean_dec(v_declHint_1833_);
v___x_1852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_c_1850_);
v___x_1854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_MessageData_note(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_msg_1832_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1915_; 
v_val_1859_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1861_ = v___x_1851_;
v_isShared_1862_ = v_isSharedCheck_1915_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_val_1859_);
lean_dec(v___x_1851_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1915_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v_modules_1864_; lean_object* v_moduleNames_1865_; lean_object* v_mod_1866_; uint8_t v___y_1868_; uint8_t v___x_1898_; 
v___x_1863_ = l_Lean_Environment_header(v_env_1838_);
lean_dec_ref(v_env_1838_);
v_modules_1864_ = lean_ctor_get(v___x_1863_, 3);
lean_inc_ref(v_modules_1864_);
v_moduleNames_1865_ = lean_ctor_get(v___x_1863_, 4);
lean_inc_ref(v_moduleNames_1865_);
lean_dec_ref(v___x_1863_);
v_mod_1866_ = lean_array_get(v___x_1836_, v_moduleNames_1865_, v_val_1859_);
lean_dec_ref(v_moduleNames_1865_);
v___x_1898_ = l_Lean_isPrivateName(v_declHint_1833_);
lean_dec(v_declHint_1833_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_modules_1864_);
v___x_1900_ = lean_nat_dec_lt(v_val_1859_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_dec_ref(v_modules_1864_);
lean_dec(v_val_1859_);
v___y_1868_ = v___x_1898_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1901_; lean_object* v_toImport_1902_; uint8_t v_isExported_1903_; 
v___x_1901_ = lean_array_fget(v_modules_1864_, v_val_1859_);
lean_dec(v_val_1859_);
lean_dec_ref(v_modules_1864_);
v_toImport_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc_ref(v_toImport_1902_);
lean_dec(v___x_1901_);
v_isExported_1903_ = lean_ctor_get_uint8(v_toImport_1902_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1902_);
v___y_1868_ = v_isExported_1903_;
goto v___jp_1867_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec_ref(v_modules_1864_);
lean_del_object(v___x_1861_);
lean_dec(v_val_1859_);
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v_c_1850_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__24);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_ofName(v_mod_1866_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__26);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_MessageData_note(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_msg_1832_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
v___jp_1867_:
{
if (v___y_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_c_1850_);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_MessageData_ofName(v_mod_1866_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_MessageData_note(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_msg_1832_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1878_);
v___x_1880_ = v___x_1861_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_c_1850_);
v___x_1884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_MessageData_ofName(v_mod_1866_);
lean_inc_ref(v___x_1886_);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1886_);
v___x_1891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__22);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MessageData_note(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_msg_1832_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1894_);
v___x_1896_ = v___x_1861_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
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
lean_object* v___x_1916_; 
lean_dec_ref(v_env_1838_);
lean_dec(v_declHint_1833_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_msg_1832_);
return v___x_1916_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1832_ = stack[0].m_obj;
lean_object* v_declHint_1833_ = stack[1].m_obj;
lean_object* v___y_1834_ = stack[2].m_obj;
lean_object* v_res_1917_;
v_res_1917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1832_, v_declHint_1833_, v___y_1834_);
stack->m_obj
 = v_res_1917_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1918_, lean_object* v_declHint_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1918_, v_declHint_1919_, v___y_1920_);
lean_dec(v___y_1920_);
return v_res_1922_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_1923_, lean_object* v_declHint_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1940_; 
v___x_1930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1923_, v_declHint_1924_, v___y_1928_);
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = l_Lean_unknownIdentifierMessageTag;
v___x_1936_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1923_ = stack[0].m_obj;
lean_object* v_declHint_1924_ = stack[1].m_obj;
lean_object* v___y_1925_ = stack[2].m_obj;
lean_object* v___y_1926_ = stack[3].m_obj;
lean_object* v___y_1927_ = stack[4].m_obj;
lean_object* v___y_1928_ = stack[5].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1923_, v_declHint_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1942_, lean_object* v_declHint_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1942_, v_declHint_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1949_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_1950_, lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_toCold_1957_; lean_object* v_currRecDepth_1958_; lean_object* v_ref_1959_; uint16_t v_optionFlags_1960_; uint8_t v_suppressElabErrors_1961_; uint8_t v_isRecordingDeps_1962_; lean_object* v_ref_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_toCold_1957_ = lean_ctor_get(v___y_1954_, 0);
v_currRecDepth_1958_ = lean_ctor_get(v___y_1954_, 1);
v_ref_1959_ = lean_ctor_get(v___y_1954_, 2);
v_optionFlags_1960_ = lean_ctor_get_uint16(v___y_1954_, sizeof(void*)*3);
v_suppressElabErrors_1961_ = lean_ctor_get_uint8(v___y_1954_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1962_ = lean_ctor_get_uint8(v___y_1954_, sizeof(void*)*3 + 3);
v_ref_1963_ = l_Lean_replaceRef(v_ref_1950_, v_ref_1959_);
lean_inc(v_currRecDepth_1958_);
lean_inc_ref(v_toCold_1957_);
v___x_1964_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1964_, 0, v_toCold_1957_);
lean_ctor_set(v___x_1964_, 1, v_currRecDepth_1958_);
lean_ctor_set(v___x_1964_, 2, v_ref_1963_);
lean_ctor_set_uint16(v___x_1964_, sizeof(void*)*3, v_optionFlags_1960_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3 + 2, v_suppressElabErrors_1961_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3 + 3, v_isRecordingDeps_1962_);
v___x_1965_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1951_, v___y_1952_, v___y_1953_, v___x_1964_, v___y_1955_);
lean_dec_ref_known(v___x_1964_, 3);
return v___x_1965_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1950_ = stack[0].m_obj;
lean_object* v_msg_1951_ = stack[1].m_obj;
lean_object* v___y_1952_ = stack[2].m_obj;
lean_object* v___y_1953_ = stack[3].m_obj;
lean_object* v___y_1954_ = stack[4].m_obj;
lean_object* v___y_1955_ = stack[5].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1950_, v_msg_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1967_, lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1967_, v_msg_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1967_);
return v_res_1974_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1975_, lean_object* v_msg_1976_, lean_object* v_declHint_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1985_; 
v___x_1983_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1976_, v_declHint_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1975_, v_a_1984_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1975_ = stack[0].m_obj;
lean_object* v_msg_1976_ = stack[1].m_obj;
lean_object* v_declHint_1977_ = stack[2].m_obj;
lean_object* v___y_1978_ = stack[3].m_obj;
lean_object* v___y_1979_ = stack[4].m_obj;
lean_object* v___y_1980_ = stack[5].m_obj;
lean_object* v___y_1981_ = stack[6].m_obj;
lean_object* v_res_1986_;
v_res_1986_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1975_, v_msg_1976_, v_declHint_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
stack->m_obj
 = v_res_1986_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1987_, lean_object* v_msg_1988_, lean_object* v_declHint_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1987_, v_msg_1988_, v_declHint_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v_ref_1987_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1999_, lean_object* v_constName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2006_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2007_ = 0;
lean_inc(v_constName_2000_);
v___x_2008_ = l_Lean_MessageData_ofConstName(v_constName_2000_, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2006_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1999_, v___x_2011_, v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2012_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1999_ = stack[0].m_obj;
lean_object* v_constName_2000_ = stack[1].m_obj;
lean_object* v___y_2001_ = stack[2].m_obj;
lean_object* v___y_2002_ = stack[3].m_obj;
lean_object* v___y_2003_ = stack[4].m_obj;
lean_object* v___y_2004_ = stack[5].m_obj;
lean_object* v_res_2013_;
v_res_2013_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_1999_, v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
stack->m_obj
 = v_res_2013_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2014_, lean_object* v_constName_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2014_, v_constName_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v_ref_2014_);
return v_res_2021_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object* v_constName_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_ref_2028_; lean_object* v___x_2029_; 
v_ref_2028_ = lean_ctor_get(v___y_2025_, 2);
v___x_2029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2028_, v_constName_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
return v___x_2029_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2022_ = stack[0].m_obj;
lean_object* v___y_2023_ = stack[1].m_obj;
lean_object* v___y_2024_ = stack[2].m_obj;
lean_object* v___y_2025_ = stack[3].m_obj;
lean_object* v___y_2026_ = stack[4].m_obj;
lean_object* v_res_2030_;
v_res_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
stack->m_obj
 = v_res_2030_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2037_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object* v_constName_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v_env_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = lean_st_ref_get(v___y_2042_);
v_env_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_ref(v_env_2045_);
lean_dec(v___x_2044_);
v___x_2046_ = 0;
lean_inc(v_constName_2038_);
v___x_2047_ = l_Lean_Environment_findConstVal_x3f(v_env_2045_, v_constName_2038_, v___x_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2048_;
}
else
{
lean_object* v_val_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_constName_2038_);
v_val_2049_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2047_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_val_2049_);
lean_dec(v___x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 0);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_val_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2038_ = stack[0].m_obj;
lean_object* v___y_2039_ = stack[1].m_obj;
lean_object* v___y_2040_ = stack[2].m_obj;
lean_object* v___y_2041_ = stack[3].m_obj;
lean_object* v___y_2042_ = stack[4].m_obj;
lean_object* v_res_2057_;
v_res_2057_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_constName_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
stack->m_obj
 = v_res_2057_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object* v_constName_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_constName_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__1(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__0));
v___x_2067_ = l_Lean_stringToMessageData(v___x_2066_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__3(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__2));
v___x_2070_ = l_Lean_stringToMessageData(v___x_2069_);
return v___x_2070_;
}
}
lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object* v_declName_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2077_; 
lean_inc(v_declName_2071_);
v___x_2077_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_declName_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2120_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2120_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2120_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2090_; lean_object* v_env_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_st_ref_get(v_a_2075_);
v_env_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc_ref(v_env_2091_);
lean_dec(v___x_2090_);
lean_inc(v_declName_2071_);
v___x_2092_ = l_Lean_wasOriginallyTheorem(v_env_2091_, v_declName_2071_);
if (v___x_2092_ == 0)
{
lean_object* v_type_2093_; lean_object* v___x_2094_; 
v_type_2093_ = lean_ctor_get(v_a_2078_, 2);
lean_inc_ref(v_type_2093_);
v___x_2094_ = l_Lean_Meta_isProp(v_type_2093_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_unbox(v_a_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_del_object(v___x_2080_);
lean_dec(v_a_2078_);
v___x_2097_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__1, &l_Lean_Meta_Grind_getProofForDecl___closed__1_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__1);
v___x_2098_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
v___x_2099_ = l_Lean_MessageData_ofConstName(v_declName_2071_, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__3, &l_Lean_Meta_Grind_getProofForDecl___closed__3_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__3);
v___x_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_2102_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_dec(v_a_2095_);
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_del_object(v___x_2080_);
lean_dec(v_a_2078_);
lean_dec(v_declName_2071_);
v_a_2112_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2094_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2094_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
goto v___jp_2082_;
}
v___jp_2082_:
{
lean_object* v_levelParams_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v_levelParams_2083_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_levelParams_2083_);
lean_dec(v_a_2078_);
v___x_2084_ = lean_box(0);
v___x_2085_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(v_levelParams_2083_, v___x_2084_);
v___x_2086_ = l_Lean_mkConst(v_declName_2071_, v___x_2085_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2086_);
v___x_2088_ = v___x_2080_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_declName_2071_);
v_a_2121_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2077_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2077_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getProofForDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2071_ = stack[0].m_obj;
lean_object* v_a_2072_ = stack[1].m_obj;
lean_object* v_a_2073_ = stack[2].m_obj;
lean_object* v_a_2074_ = stack[3].m_obj;
lean_object* v_a_2075_ = stack[4].m_obj;
lean_object* v_res_2129_;
v_res_2129_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
stack->m_obj
 = v_res_2129_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object* v_declName_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2136_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object* v_00_u03b1_2137_, lean_object* v_constName_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2138_ = stack[1].m_obj;
lean_object* v___y_2139_ = stack[2].m_obj;
lean_object* v___y_2140_ = stack[3].m_obj;
lean_object* v___y_2141_ = stack[4].m_obj;
lean_object* v___y_2142_ = stack[5].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_box(0), v_constName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_constName_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(v_00_u03b1_2146_, v_constName_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2153_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2154_, lean_object* v_ref_2155_, lean_object* v_constName_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2155_, v_constName_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2155_ = stack[1].m_obj;
lean_object* v_constName_2156_ = stack[2].m_obj;
lean_object* v___y_2157_ = stack[3].m_obj;
lean_object* v___y_2158_ = stack[4].m_obj;
lean_object* v___y_2159_ = stack[5].m_obj;
lean_object* v___y_2160_ = stack[6].m_obj;
lean_object* v_res_2163_;
v_res_2163_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_box(0), v_ref_2155_, v_constName_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
stack->m_obj
 = v_res_2163_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2164_, lean_object* v_ref_2165_, lean_object* v_constName_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(v_00_u03b1_2164_, v_ref_2165_, v_constName_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v_ref_2165_);
return v_res_2172_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2173_, lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v_declHint_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2174_, v_msg_2175_, v_declHint_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2174_ = stack[1].m_obj;
lean_object* v_msg_2175_ = stack[2].m_obj;
lean_object* v_declHint_2176_ = stack[3].m_obj;
lean_object* v___y_2177_ = stack[4].m_obj;
lean_object* v___y_2178_ = stack[5].m_obj;
lean_object* v___y_2179_ = stack[6].m_obj;
lean_object* v___y_2180_ = stack[7].m_obj;
lean_object* v_res_2183_;
v_res_2183_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_ref_2174_, v_msg_2175_, v_declHint_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
stack->m_obj
 = v_res_2183_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_ref_2185_, lean_object* v_msg_2186_, lean_object* v_declHint_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2184_, v_ref_2185_, v_msg_2186_, v_declHint_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v_ref_2185_);
return v_res_2193_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2194_, lean_object* v_declHint_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2194_, v_declHint_2195_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2194_ = stack[0].m_obj;
lean_object* v_declHint_2195_ = stack[1].m_obj;
lean_object* v___y_2196_ = stack[2].m_obj;
lean_object* v___y_2197_ = stack[3].m_obj;
lean_object* v___y_2198_ = stack[4].m_obj;
lean_object* v___y_2199_ = stack[5].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2194_, v_declHint_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2203_, lean_object* v_declHint_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2203_, v_declHint_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2210_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2211_, lean_object* v_ref_2212_, lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2212_, v_msg_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2212_ = stack[1].m_obj;
lean_object* v_msg_2213_ = stack[2].m_obj;
lean_object* v___y_2214_ = stack[3].m_obj;
lean_object* v___y_2215_ = stack[4].m_obj;
lean_object* v___y_2216_ = stack[5].m_obj;
lean_object* v___y_2217_ = stack[6].m_obj;
lean_object* v_res_2220_;
v_res_2220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_box(0), v_ref_2212_, v_msg_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
stack->m_obj
 = v_res_2220_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_ref_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2221_, v_ref_2222_, v_msg_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v_ref_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object* v___x_2230_, lean_object* v___x_2231_, lean_object* v_sym_2232_, lean_object* v_next_2233_, lean_object* v_acc_2234_, lean_object* v_h_2235_, lean_object* v_G_2236_){
_start:
{
lean_object* v_a_2238_; uint8_t v___x_2242_; 
v___x_2242_ = lean_nat_dec_lt(v_next_2233_, v___x_2230_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v_G_2236_);
lean_dec(v_sym_2232_);
return v_acc_2234_;
}
else
{
lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2273_; 
v_fst_2243_ = lean_ctor_get(v_acc_2234_, 0);
v_snd_2244_ = lean_ctor_get(v_acc_2234_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_acc_2234_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2246_ = v_acc_2234_;
v_isShared_2247_ = v_isSharedCheck_2273_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2243_);
lean_dec(v_acc_2234_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2273_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v_smap_2249_; lean_object* v_origins_2250_; lean_object* v_erased_2251_; lean_object* v_omap_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2272_; 
v___x_2248_ = lean_array_get(v___x_2231_, v_snd_2244_, v_next_2233_);
v_smap_2249_ = lean_ctor_get(v___x_2248_, 0);
v_origins_2250_ = lean_ctor_get(v___x_2248_, 1);
v_erased_2251_ = lean_ctor_get(v___x_2248_, 2);
v_omap_2252_ = lean_ctor_get(v___x_2248_, 3);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2254_ = v___x_2248_;
v_isShared_2255_ = v_isSharedCheck_2272_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_omap_2252_);
lean_inc(v_erased_2251_);
lean_inc(v_origins_2250_);
lean_inc(v_smap_2249_);
lean_dec(v___x_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2272_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_2257_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_2232_);
v___x_2258_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2256_, v___x_2257_, v_smap_2249_, v_sym_2232_);
if (lean_obj_tag(v___x_2258_) == 1)
{
lean_object* v_val_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = l_Lean_PersistentHashMap_erase___redArg(v___x_2256_, v___x_2257_, v_smap_2249_, v_sym_2232_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2260_);
v___x_2262_ = v___x_2254_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_origins_2250_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_erased_2251_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_omap_2252_);
v___x_2262_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2263_ = l_List_appendTR___redArg(v_fst_2243_, v_val_2259_);
v___x_2264_ = lean_array_set(v_snd_2244_, v_next_2233_, v___x_2262_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2264_);
lean_ctor_set(v___x_2246_, 0, v___x_2263_);
v___x_2266_ = v___x_2246_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v_a_2238_ = v___x_2266_;
goto v___jp_2237_;
}
}
}
else
{
lean_object* v___x_2270_; 
lean_dec(v___x_2258_);
lean_del_object(v___x_2254_);
lean_dec_ref(v_omap_2252_);
lean_dec_ref(v_erased_2251_);
lean_dec_ref(v_origins_2250_);
lean_dec_ref(v_smap_2249_);
lean_dec(v_sym_2232_);
if (v_isShared_2247_ == 0)
{
v___x_2270_ = v___x_2246_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_fst_2243_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_snd_2244_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
v_a_2238_ = v___x_2270_;
goto v___jp_2237_;
}
}
}
}
}
v___jp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_next_2233_, v___x_2239_);
v___x_2241_ = lean_apply_4(v_G_2236_, v___x_2240_, v_a_2238_, lean_box(0), lean_box(0));
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v_sym_2276_, lean_object* v_next_2277_, lean_object* v_acc_2278_, lean_object* v_h_2279_, lean_object* v_G_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(v___x_2274_, v___x_2275_, v_sym_2276_, v_next_2277_, v_acc_2278_, v_h_2279_, v_G_2280_);
lean_dec(v_next_2277_);
lean_dec_ref(v___x_2275_);
lean_dec(v___x_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object* v_s_2282_, lean_object* v_sym_2283_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v_result_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2302_; 
v___x_2284_ = lean_array_get_size(v_s_2282_);
v___x_2285_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2286_, 0, v___x_2284_);
lean_closure_set(v___f_2286_, 1, v___x_2285_);
lean_closure_set(v___f_2286_, 2, v_sym_2283_);
v___x_2287_ = lean_unsigned_to_nat(0u);
v_result_2288_ = lean_box(0);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_result_2288_);
lean_ctor_set(v___x_2289_, 1, v_s_2282_);
v___x_2290_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2286_, v___x_2287_, v___x_2289_, lean_box(0));
v_fst_2291_ = lean_ctor_get(v___x_2290_, 0);
v_snd_2292_ = lean_ctor_get(v___x_2290_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2294_ = v___x_2290_;
v_isShared_2295_ = v_isSharedCheck_2302_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_snd_2292_);
lean_inc(v_fst_2291_);
lean_dec(v___x_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2302_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
uint8_t v___x_2296_; 
v___x_2296_ = l_List_isEmpty___redArg(v_fst_2291_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2298_; 
if (v_isShared_2295_ == 0)
{
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_snd_2292_);
v___x_2298_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
else
{
lean_object* v___x_2301_; 
lean_del_object(v___x_2294_);
lean_dec(v_snd_2292_);
lean_dec(v_fst_2291_);
v___x_2301_ = lean_box(0);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object* v_00_u03b1_2303_, lean_object* v_s_2304_, lean_object* v_sym_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(v_s_2304_, v_sym_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v_thms_2310_; 
v___x_2308_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0);
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg___closed__0);
v_thms_2310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_thms_2310_, 0, v___x_2309_);
lean_ctor_set(v_thms_2310_, 1, v___x_2308_);
lean_ctor_set(v_thms_2310_, 2, v___x_2308_);
lean_ctor_set(v_thms_2310_, 3, v___x_2309_);
return v_thms_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object* v_inst_2311_, lean_object* v_s_2312_, lean_object* v_thm_2313_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = lean_array_get_size(v_s_2312_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_nat_dec_eq(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_nat_dec_lt(v___x_2315_, v___x_2314_);
if (v___x_2317_ == 0)
{
lean_dec(v_thm_2313_);
lean_dec_ref(v_inst_2311_);
return v_s_2312_;
}
else
{
lean_object* v_v_2318_; lean_object* v___x_2319_; lean_object* v_xs_x27_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_v_2318_ = lean_array_fget(v_s_2312_, v___x_2315_);
v___x_2319_ = lean_box(0);
v_xs_x27_2320_ = lean_array_fset(v_s_2312_, v___x_2315_, v___x_2319_);
v___x_2321_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2311_, v_v_2318_, v_thm_2313_);
v___x_2322_ = lean_array_fset(v_xs_x27_2320_, v___x_2315_, v___x_2321_);
return v___x_2322_;
}
}
else
{
lean_object* v_thms_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_s_2312_);
v_thms_2323_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1);
v___x_2324_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2311_, v_thms_2323_, v_thm_2313_);
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_mk_empty_array_with_capacity(v___x_2325_);
v___x_2327_ = lean_array_push(v___x_2326_, v___x_2324_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object* v_00_u03b1_2328_, lean_object* v_inst_2329_, lean_object* v_s_2330_, lean_object* v_thm_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Meta_Grind_TheoremsArray_insert___redArg(v_inst_2329_, v_s_2330_, v_thm_2331_);
return v___x_2332_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object* v_origin_2333_, lean_object* v_as_2334_, size_t v_i_2335_, size_t v_stop_2336_){
_start:
{
uint8_t v___x_2337_; 
v___x_2337_ = lean_usize_dec_eq(v_i_2335_, v_stop_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v_erased_2339_; uint8_t v___x_2340_; 
v___x_2338_ = lean_array_uget_borrowed(v_as_2334_, v_i_2335_);
v_erased_2339_ = lean_ctor_get(v___x_2338_, 2);
v___x_2340_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_2339_, v_origin_2333_);
if (v___x_2340_ == 0)
{
size_t v___x_2341_; size_t v___x_2342_; 
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2335_, v___x_2341_);
v_i_2335_ = v___x_2342_;
goto _start;
}
else
{
return v___x_2340_;
}
}
else
{
uint8_t v___x_2344_; 
v___x_2344_ = 0;
return v___x_2344_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_origin_2333_ = stack[0].m_obj;
lean_object* v_as_2334_ = stack[1].m_obj;
size_t v_i_2335_ = stack[2].m_num;
size_t v_stop_2336_ = stack[3].m_num;
uint8_t v_res_2345_;
v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2333_, v_as_2334_, v_i_2335_, v_stop_2336_);
stack->m_num = v_res_2345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object* v_origin_2346_, lean_object* v_as_2347_, lean_object* v_i_2348_, lean_object* v_stop_2349_){
_start:
{
size_t v_i_boxed_2350_; size_t v_stop_boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_i_boxed_2350_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_stop_boxed_2351_ = lean_unbox_usize(v_stop_2349_);
lean_dec(v_stop_2349_);
v_res_2352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2346_, v_as_2347_, v_i_boxed_2350_, v_stop_boxed_2351_);
lean_dec_ref(v_as_2347_);
lean_dec_ref(v_origin_2346_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object* v_s_2354_, lean_object* v_origin_2355_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_array_get_size(v_s_2354_);
v___x_2358_ = lean_nat_dec_lt(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
return v___x_2358_;
}
else
{
if (v___x_2358_ == 0)
{
return v___x_2358_;
}
else
{
size_t v___x_2359_; size_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = lean_usize_of_nat(v___x_2357_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2355_, v_s_2354_, v___x_2359_, v___x_2360_);
return v___x_2361_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_TheoremsArray_isErased___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2354_ = stack[0].m_obj;
lean_object* v_origin_2355_ = stack[1].m_obj;
uint8_t v_res_2362_;
v_res_2362_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2354_, v_origin_2355_);
stack->m_num = v_res_2362_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object* v_s_2363_, lean_object* v_origin_2364_){
_start:
{
uint8_t v_res_2365_; lean_object* v_r_2366_; 
v_res_2365_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2363_, v_origin_2364_);
lean_dec_ref(v_origin_2364_);
lean_dec_ref(v_s_2363_);
v_r_2366_ = lean_box(v_res_2365_);
return v_r_2366_;
}
}
uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object* v_00_u03b1_2367_, lean_object* v_s_2368_, lean_object* v_origin_2369_){
_start:
{
uint8_t v___x_2370_; 
v___x_2370_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2368_, v_origin_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_TheoremsArray_isErased_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2368_ = stack[1].m_obj;
lean_object* v_origin_2369_ = stack[2].m_obj;
uint8_t v_res_2371_;
v_res_2371_ = l_Lean_Meta_Grind_TheoremsArray_isErased(lean_box(0), v_s_2368_, v_origin_2369_);
stack->m_num = v_res_2371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object* v_00_u03b1_2372_, lean_object* v_s_2373_, lean_object* v_origin_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_Meta_Grind_TheoremsArray_isErased(v_00_u03b1_2372_, v_s_2373_, v_origin_2374_);
lean_dec_ref(v_origin_2374_);
lean_dec_ref(v_s_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object* v_00_u03b1_2377_, lean_object* v_origin_2378_, lean_object* v_as_2379_, size_t v_i_2380_, size_t v_stop_2381_){
_start:
{
uint8_t v___x_2382_; 
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2378_, v_as_2379_, v_i_2380_, v_stop_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_origin_2378_ = stack[1].m_obj;
lean_object* v_as_2379_ = stack[2].m_obj;
size_t v_i_2380_ = stack[3].m_num;
size_t v_stop_2381_ = stack[4].m_num;
uint8_t v_res_2383_;
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_box(0), v_origin_2378_, v_as_2379_, v_i_2380_, v_stop_2381_);
stack->m_num = v_res_2383_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object* v_00_u03b1_2384_, lean_object* v_origin_2385_, lean_object* v_as_2386_, lean_object* v_i_2387_, lean_object* v_stop_2388_){
_start:
{
size_t v_i_boxed_2389_; size_t v_stop_boxed_2390_; uint8_t v_res_2391_; lean_object* v_r_2392_; 
v_i_boxed_2389_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_stop_boxed_2390_ = lean_unbox_usize(v_stop_2388_);
lean_dec(v_stop_2388_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(v_00_u03b1_2384_, v_origin_2385_, v_as_2386_, v_i_boxed_2389_, v_stop_boxed_2390_);
lean_dec_ref(v_as_2386_);
lean_dec_ref(v_origin_2385_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object* v_upperBound_2393_, lean_object* v_s_2394_, lean_object* v_origin_2395_, lean_object* v_a_2396_, lean_object* v_b_2397_){
_start:
{
lean_object* v_a_2399_; uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_lt(v_a_2396_, v_upperBound_2393_);
if (v___x_2403_ == 0)
{
lean_dec(v_a_2396_);
return v_b_2397_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_array_fget_borrowed(v_s_2394_, v_a_2396_);
v___x_2405_ = l_Lean_Meta_Grind_Theorems_find___redArg(v___x_2404_, v_origin_2395_);
v___x_2406_ = l_List_isEmpty___redArg(v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = l_List_appendTR___redArg(v_b_2397_, v___x_2405_);
v_a_2399_ = v___x_2407_;
goto v___jp_2398_;
}
else
{
lean_dec(v___x_2405_);
v_a_2399_ = v_b_2397_;
goto v___jp_2398_;
}
}
v___jp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_add(v_a_2396_, v___x_2400_);
lean_dec(v_a_2396_);
v_a_2396_ = v___x_2401_;
v_b_2397_ = v_a_2399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_2408_, lean_object* v_s_2409_, lean_object* v_origin_2410_, lean_object* v_a_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2408_, v_s_2409_, v_origin_2410_, v_a_2411_, v_b_2412_);
lean_dec_ref(v_origin_2410_);
lean_dec_ref(v_s_2409_);
lean_dec(v_upperBound_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object* v_s_2414_, lean_object* v_origin_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_r_2418_; lean_object* v___x_2419_; 
v___x_2416_ = lean_array_get_size(v_s_2414_);
v___x_2417_ = lean_unsigned_to_nat(0u);
v_r_2418_ = lean_box(0);
v___x_2419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v___x_2416_, v_s_2414_, v_origin_2415_, v___x_2417_, v_r_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object* v_s_2420_, lean_object* v_origin_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2420_, v_origin_2421_);
lean_dec_ref(v_origin_2421_);
lean_dec_ref(v_s_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object* v_00_u03b1_2423_, lean_object* v_s_2424_, lean_object* v_origin_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2424_, v_origin_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_s_2428_, lean_object* v_origin_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Meta_Grind_TheoremsArray_find(v_00_u03b1_2427_, v_s_2428_, v_origin_2429_);
lean_dec_ref(v_origin_2429_);
lean_dec_ref(v_s_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object* v_00_u03b1_2431_, lean_object* v_upperBound_2432_, lean_object* v_s_2433_, lean_object* v_origin_2434_, lean_object* v_inst_2435_, lean_object* v_R_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_, lean_object* v_c_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2432_, v_s_2433_, v_origin_2434_, v_a_2437_, v_b_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object* v_00_u03b1_2441_, lean_object* v_upperBound_2442_, lean_object* v_s_2443_, lean_object* v_origin_2444_, lean_object* v_inst_2445_, lean_object* v_R_2446_, lean_object* v_a_2447_, lean_object* v_b_2448_, lean_object* v_c_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(v_00_u03b1_2441_, v_upperBound_2442_, v_s_2443_, v_origin_2444_, v_inst_2445_, v_R_2446_, v_a_2447_, v_b_2448_, v_c_2449_);
lean_dec_ref(v_origin_2444_);
lean_dec_ref(v_s_2443_);
lean_dec(v_upperBound_2442_);
return v_res_2450_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
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
