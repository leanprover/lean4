// Lean compiler output
// Module: Lean.Meta.Tactic.NormCast
// Imports: public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.CoeAttr
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpEntry_default;
lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_Label_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_instDecidableEqLabel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instDecidableEqLabel___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.NormCast.Label.elim"};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__0 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__1 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.NormCast.Label.move"};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__2 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__3 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.NormCast.Label.squash"};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__4 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_NormCast_instReprLabel_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__5 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_NormCast_instReprLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_NormCast_instReprLabel_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_NormCast_instReprLabel___closed__0 = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_NormCast_instReprLabel = (const lean_object*)&l_Lean_Meta_NormCast_instReprLabel___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_instInhabitedLabel_default;
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_instInhabitedLabel;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_NormCast_getSimpArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_getSimpArgs___closed__0;
static const lean_array_object l_Lean_Meta_NormCast_getSimpArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_NormCast_getSimpArgs___closed__1 = (const lean_object*)&l_Lean_Meta_NormCast_getSimpArgs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "Invalid `norm_cast` squash lemma: The right-hand side must have fewer coe functions in head position than the left-hand side"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "Invalid `norm_cast` lemma: The right-hand side cannot start with a coe function"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "coe functions are registered using the `[coe]` attribute"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "Invalid `norm_cast` lemma: At least one coe function must appear in the left-hand side"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__10_value;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_NormCast_classifyType___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Invalid `norm_cast` lemma: Expected an equality or iff, but found"};
static const lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_NormCast_classifyType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_NormCast_classifyType___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_NormCast_classifyType___closed__0 = (const lean_object*)&l_Lean_Meta_NormCast_classifyType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "push_cast"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 141, 166, 133, 48, 139, 32, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "The `push_cast` simp attribute uses `norm_cast` lemmas to move casts toward the leaf nodes of the expression."};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NormCast"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pushCastExt"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 252, 139, 167, 101, 24, 122, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 15, 215, 232, 47, 30, 51, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_pushCastExt;
static lean_once_cell_t l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0;
static lean_once_cell_t l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instInhabitedNormCastExtension;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "normCastExt"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 252, 139, 167, 101, 24, 122, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 160, 192, 50, 161, 126, 238, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "up"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 239, 154, 203, 238, 189, 173, 170)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "down"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 248, 244, 126, 29, 150, 156, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "squash"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 222, 252, 90, 152, 82, 120, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_normCastExt;
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "move"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Tactic.NormCast"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "_private.Lean.Meta.Tactic.NormCast.0.Lean.Meta.NormCast.initFn._@.Lean.Meta.Tactic.NormCast.1115639401._hygCtx._hyg.2"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normCastLabel"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 95, 179, 75, 215, 219, 242, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(224, 133, 209, 101, 18, 23, 252, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(153, 116, 178, 210, 227, 81, 251, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 40, 4, 248, 10, 81, 144, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 105, 54, 5, 173, 232, 171, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__11_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 134, 103, 73, 210, 182, 222, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__12_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__13_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 28, 59, 91, 47, 182, 184, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__14_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 157, 47, 223, 53, 127, 124, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__15_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 172, 207, 13, 42, 233, 2, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__16_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 202, 61, 98, 38, 38, 146, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__17_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 251, 211, 84, 159, 202, 182, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__18_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1115639401) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 44, 99, 111, 2, 135, 110, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__19_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__20_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 48, 238, 178, 132, 172, 253, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__21_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__22_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 9, 245, 39, 178, 28, 105, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__23_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(67, 113, 250, 183, 96, 106, 133, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_cast"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 164, 114, 243, 79, 127, 187, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "attribute for norm_cast"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__24_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__27_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__29_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__30_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__28_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_NormCast_Label_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_NormCast_Label_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_NormCast_Label_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg(lean_object* v_elim_22_){
_start:
{
lean_inc(v_elim_22_);
return v_elim_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg___boxed(lean_object* v_elim_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_NormCast_Label_elim_elim___redArg(v_elim_23_);
lean_dec(v_elim_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_elim_28_){
_start:
{
lean_inc(v_elim_28_);
return v_elim_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_elim_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_NormCast_Label_elim_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_elim_32_);
lean_dec(v_elim_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg(lean_object* v_move_35_){
_start:
{
lean_inc(v_move_35_);
return v_move_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg___boxed(lean_object* v_move_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_NormCast_Label_move_elim___redArg(v_move_36_);
lean_dec(v_move_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_move_41_){
_start:
{
lean_inc(v_move_41_);
return v_move_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_move_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_NormCast_Label_move_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_move_45_);
lean_dec(v_move_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg(lean_object* v_squash_48_){
_start:
{
lean_inc(v_squash_48_);
return v_squash_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg___boxed(lean_object* v_squash_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_NormCast_Label_squash_elim___redArg(v_squash_49_);
lean_dec(v_squash_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_squash_54_){
_start:
{
lean_inc(v_squash_54_);
return v_squash_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_squash_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_NormCast_Label_squash_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_squash_58_);
lean_dec(v_squash_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_Label_ofNat(lean_object* v_n_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_nat_dec_le(v_n_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_dec_le(v_n_61_, v___x_64_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 2;
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 1;
return v___x_67_;
}
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ofNat___boxed(lean_object* v_n_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_Meta_NormCast_Label_ofNat(v_n_69_);
lean_dec(v_n_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_instDecidableEqLabel(uint8_t v_x_72_, uint8_t v_y_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_74_ = lean_box(v_x_72_);
v___x_75_ = lean_obj_tag_nat(v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_box(v_y_73_);
v___x_77_ = lean_obj_tag_nat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_nat_dec_eq(v___x_75_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instDecidableEqLabel___boxed(lean_object* v_x_79_, lean_object* v_y_80_){
_start:
{
uint8_t v_x_23__boxed_81_; uint8_t v_y_24__boxed_82_; uint8_t v_res_83_; lean_object* v_r_84_; 
v_x_23__boxed_81_ = lean_unbox(v_x_79_);
v_y_24__boxed_82_ = lean_unbox(v_y_80_);
v_res_83_ = l_Lean_Meta_NormCast_instDecidableEqLabel(v_x_23__boxed_81_, v_y_24__boxed_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(2u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr(uint8_t v_x_98_, lean_object* v_prec_99_){
_start:
{
lean_object* v___y_101_; lean_object* v___y_108_; lean_object* v___y_115_; 
switch(v_x_98_)
{
case 0:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1024u);
v___x_122_ = lean_nat_dec_le(v___x_121_, v_prec_99_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_101_ = v___x_123_;
goto v___jp_100_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_101_ = v___x_124_;
goto v___jp_100_;
}
}
case 1:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_99_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_108_ = v___x_127_;
goto v___jp_107_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_108_ = v___x_128_;
goto v___jp_107_;
}
}
default: 
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = lean_nat_dec_le(v___x_129_, v_prec_99_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_115_ = v___x_131_;
goto v___jp_114_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_115_ = v___x_132_;
goto v___jp_114_;
}
}
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__1));
lean_inc(v___y_101_);
v___x_103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = 0;
v___x_105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
v___x_106_ = l_Repr_addAppParen(v___x_105_, v_prec_99_);
return v___x_106_;
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__3));
lean_inc(v___y_108_);
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_99_);
return v___x_113_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_116_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__5));
lean_inc(v___y_115_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___y_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = l_Repr_addAppParen(v___x_119_, v_prec_99_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___boxed(lean_object* v_x_133_, lean_object* v_prec_134_){
_start:
{
uint8_t v_x_171__boxed_135_; lean_object* v_res_136_; 
v_x_171__boxed_135_ = lean_unbox(v_x_133_);
v_res_136_ = l_Lean_Meta_NormCast_instReprLabel_repr(v_x_171__boxed_135_, v_prec_134_);
lean_dec(v_prec_134_);
return v_res_136_;
}
}
static uint8_t _init_l_Lean_Meta_NormCast_instInhabitedLabel_default(void){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
static uint8_t _init_l_Lean_Meta_NormCast_instInhabitedLabel(void){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(lean_object* v_as_141_, size_t v_sz_142_, size_t v_i_143_, lean_object* v_b_144_){
_start:
{
lean_object* v_a_147_; uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_lt(v_i_143_, v_sz_142_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v_b_144_);
return v___x_152_;
}
else
{
lean_object* v_snd_153_; lean_object* v_fst_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_188_; 
v_snd_153_ = lean_ctor_get(v_b_144_, 1);
v_fst_154_ = lean_ctor_get(v_b_144_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_b_144_);
if (v_isSharedCheck_188_ == 0)
{
v___x_156_ = v_b_144_;
v_isShared_157_ = v_isSharedCheck_188_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_153_);
lean_inc(v_fst_154_);
lean_dec(v_b_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_188_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_array_158_; lean_object* v_start_159_; lean_object* v_stop_160_; uint8_t v___x_161_; 
v_array_158_ = lean_ctor_get(v_snd_153_, 0);
v_start_159_ = lean_ctor_get(v_snd_153_, 1);
v_stop_160_ = lean_ctor_get(v_snd_153_, 2);
v___x_161_ = lean_nat_dec_lt(v_start_159_, v_stop_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_163_; 
if (v_isShared_157_ == 0)
{
v___x_163_ = v___x_156_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_fst_154_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_snd_153_);
v___x_163_ = v_reuseFailAlloc_165_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_184_; 
lean_inc(v_stop_160_);
lean_inc(v_start_159_);
lean_inc_ref(v_array_158_);
v_isSharedCheck_184_ = !lean_is_exclusive(v_snd_153_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_185_ = lean_ctor_get(v_snd_153_, 2);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_snd_153_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_snd_153_, 0);
lean_dec(v_unused_187_);
v___x_167_ = v_snd_153_;
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
else
{
lean_dec(v_snd_153_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_169_ = lean_array_fget(v_array_158_, v_start_159_);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_start_159_, v___x_170_);
lean_dec(v_start_159_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_171_);
v___x_173_ = v___x_167_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_array_158_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_stop_160_);
v___x_173_ = v_reuseFailAlloc_183_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
uint8_t v___x_174_; 
v___x_174_ = lean_unbox(v___x_169_);
lean_dec(v___x_169_);
if (v___x_174_ == 2)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v_a_175_ = lean_array_uget_borrowed(v_as_141_, v_i_143_);
lean_inc(v_a_175_);
v___x_176_ = lean_array_push(v_fst_154_, v_a_175_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_173_);
lean_ctor_set(v___x_156_, 0, v___x_176_);
v___x_178_ = v___x_156_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v_a_147_ = v___x_178_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_181_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_173_);
v___x_181_ = v___x_156_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_154_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_173_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
v_a_147_ = v___x_181_;
goto v___jp_146_;
}
}
}
}
}
}
}
v___jp_146_:
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_143_, v___x_148_);
v_i_143_ = v___x_149_;
v_b_144_ = v_a_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg___boxed(lean_object* v_as_189_, lean_object* v_sz_190_, lean_object* v_i_191_, lean_object* v_b_192_, lean_object* v___y_193_){
_start:
{
size_t v_sz_boxed_194_; size_t v_i_boxed_195_; lean_object* v_res_196_; 
v_sz_boxed_194_ = lean_unbox_usize(v_sz_190_);
lean_dec(v_sz_190_);
v_i_boxed_195_ = lean_unbox_usize(v_i_191_);
lean_dec(v_i_191_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_189_, v_sz_boxed_194_, v_i_boxed_195_, v_b_192_);
lean_dec_ref(v_as_189_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v_dummy_198_; 
v___x_197_ = lean_box(0);
v_dummy_198_ = l_Lean_Expr_sort___override(v___x_197_);
return v_dummy_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs(lean_object* v_e_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = l_Lean_Expr_getAppFn(v_e_201_);
v___x_208_ = 1;
v___x_209_ = lean_box(0);
v___x_210_ = l_Lean_Meta_mkCongrSimp_x3f(v___x_207_, v___x_208_, v___x_209_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_257_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_257_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_257_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_257_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
if (lean_obj_tag(v_a_211_) == 0)
{
lean_object* v_dummy_215_; lean_object* v_nargs_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_dummy_215_ = lean_obj_once(&l_Lean_Meta_NormCast_getSimpArgs___closed__0, &l_Lean_Meta_NormCast_getSimpArgs___closed__0_once, _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0);
v_nargs_216_ = l_Lean_Expr_getAppNumArgs(v_e_201_);
lean_inc(v_nargs_216_);
v___x_217_ = lean_mk_array(v_nargs_216_, v_dummy_215_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_sub(v_nargs_216_, v___x_218_);
lean_dec(v_nargs_216_);
v___x_220_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_201_, v___x_217_, v___x_219_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_220_);
v___x_222_ = v___x_213_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_object* v_val_224_; lean_object* v_argKinds_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_dummy_230_; lean_object* v_nargs_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; size_t v_sz_237_; size_t v___x_238_; lean_object* v___x_239_; 
lean_del_object(v___x_213_);
v_val_224_ = lean_ctor_get(v_a_211_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v_a_211_, 1);
v_argKinds_225_ = lean_ctor_get(v_val_224_, 2);
lean_inc_ref(v_argKinds_225_);
lean_dec(v_val_224_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = ((lean_object*)(l_Lean_Meta_NormCast_getSimpArgs___closed__1));
v___x_228_ = lean_array_get_size(v_argKinds_225_);
v___x_229_ = l_Array_toSubarray___redArg(v_argKinds_225_, v___x_226_, v___x_228_);
v_dummy_230_ = lean_obj_once(&l_Lean_Meta_NormCast_getSimpArgs___closed__0, &l_Lean_Meta_NormCast_getSimpArgs___closed__0_once, _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0);
v_nargs_231_ = l_Lean_Expr_getAppNumArgs(v_e_201_);
lean_inc(v_nargs_231_);
v___x_232_ = lean_mk_array(v_nargs_231_, v_dummy_230_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_sub(v_nargs_231_, v___x_233_);
lean_dec(v_nargs_231_);
v___x_235_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_201_, v___x_232_, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_227_);
lean_ctor_set(v___x_236_, 1, v___x_229_);
v_sz_237_ = lean_array_size(v___x_235_);
v___x_238_ = ((size_t)0ULL);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v___x_235_, v_sz_237_, v___x_238_, v___x_236_);
lean_dec_ref(v___x_235_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_fst_244_; lean_object* v___x_246_; 
v_fst_244_ = lean_ctor_get(v_a_240_, 0);
lean_inc(v_fst_244_);
lean_dec(v_a_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v_fst_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_fst_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_239_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_239_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v_e_201_);
v_a_258_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_210_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_210_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs___boxed(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_NormCast_getSimpArgs(v_e_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(lean_object* v_as_273_, size_t v_sz_274_, size_t v_i_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_273_, v_sz_274_, v_i_275_, v_b_276_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___boxed(lean_object* v_as_283_, lean_object* v_sz_284_, lean_object* v_i_285_, lean_object* v_b_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_284_);
lean_dec(v_sz_284_);
v_i_boxed_293_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(v_as_283_, v_sz_boxed_292_, v_i_boxed_293_, v_b_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec_ref(v_as_283_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg(lean_object* v_e_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Expr_getAppFn(v_e_295_);
if (lean_obj_tag(v___x_301_) == 4)
{
lean_object* v_declName_302_; lean_object* v___x_303_; 
v_declName_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_declName_302_);
lean_dec_ref_known(v___x_301_, 2);
v___x_303_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_302_, v_a_296_);
lean_dec(v_declName_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
if (lean_obj_tag(v_a_304_) == 1)
{
lean_object* v_val_305_; lean_object* v_numArgs_306_; lean_object* v_coercee_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_val_305_ = lean_ctor_get(v_a_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_a_304_, 1);
v_numArgs_306_ = lean_ctor_get(v_val_305_, 0);
lean_inc(v_numArgs_306_);
v_coercee_307_ = lean_ctor_get(v_val_305_, 1);
lean_inc(v_coercee_307_);
lean_dec(v_val_305_);
v___x_308_ = l_Lean_Expr_getAppNumArgs(v_e_295_);
v___x_309_ = lean_nat_dec_le(v_numArgs_306_, v___x_308_);
lean_dec(v_numArgs_306_);
if (v___x_309_ == 0)
{
lean_dec(v___x_308_);
lean_dec(v_coercee_307_);
goto v___jp_298_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = lean_nat_sub(v___x_308_, v_coercee_307_);
lean_dec(v_coercee_307_);
lean_dec(v___x_308_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_sub(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
v___x_313_ = l_Lean_Expr_getRevArg_x21(v_e_295_, v___x_312_);
v___x_314_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___x_313_, v_a_296_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_nat_add(v_a_315_, v___x_311_);
lean_dec(v_a_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
return v___x_314_;
}
}
}
else
{
lean_dec(v_a_304_);
goto v___jp_298_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_a_324_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_303_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_303_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg___boxed(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_e_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_336_, v_a_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___boxed(lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_NormCast_countHeadCoes(v_e_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_e_343_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(lean_object* v_k_350_, lean_object* v_b_351_, lean_object* v_c_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
v___x_358_ = lean_apply_7(v_k_350_, v_b_351_, v_c_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, lean_box(0));
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed(lean_object* v_k_359_, lean_object* v_b_360_, lean_object* v_c_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(v_k_359_, v_b_360_, v_c_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(lean_object* v_e_368_, lean_object* v_k_369_, uint8_t v_cleanupAnnotations_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___f_376_; uint8_t v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_376_, 0, v_k_369_);
v___x_377_ = 1;
v___x_378_ = 0;
v___x_379_ = lean_box(0);
v___x_380_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_368_, v___x_377_, v___x_378_, v___x_377_, v___x_378_, v___x_379_, v___f_376_, v_cleanupAnnotations_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_a_389_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_380_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_380_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___boxed(lean_object* v_e_397_, lean_object* v_k_398_, lean_object* v_cleanupAnnotations_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_405_; lean_object* v_res_406_; 
v_cleanupAnnotations_boxed_405_ = lean_unbox(v_cleanupAnnotations_399_);
v_res_406_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_397_, v_k_398_, v_cleanupAnnotations_boxed_405_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(lean_object* v_00_u03b1_407_, lean_object* v_e_408_, lean_object* v_k_409_, uint8_t v_cleanupAnnotations_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_408_, v_k_409_, v_cleanupAnnotations_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___boxed(lean_object* v_00_u03b1_417_, lean_object* v_e_418_, lean_object* v_k_419_, lean_object* v_cleanupAnnotations_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_426_; lean_object* v_res_427_; 
v_cleanupAnnotations_boxed_426_ = lean_unbox(v_cleanupAnnotations_420_);
v_res_427_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(v_00_u03b1_417_, v_e_418_, v_k_419_, v_cleanupAnnotations_boxed_426_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; size_t v___x_435_; size_t v___x_436_; 
v___x_433_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
v___x_434_ = lean_nat_add(v_b_431_, v___x_433_);
lean_dec(v_b_431_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_429_, v___x_435_);
v_i_429_ = v___x_436_;
v_b_431_ = v___x_434_;
goto _start;
}
else
{
return v_b_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1___boxed(lean_object* v_as_438_, lean_object* v_i_439_, lean_object* v_stop_440_, lean_object* v_b_441_){
_start:
{
size_t v_i_boxed_442_; size_t v_stop_boxed_443_; lean_object* v_res_444_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_stop_boxed_443_ = lean_unbox_usize(v_stop_440_);
lean_dec(v_stop_440_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_as_438_, v_i_boxed_442_, v_stop_boxed_443_, v_b_441_);
lean_dec_ref(v_as_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(size_t v_sz_445_, size_t v_i_446_, lean_object* v_bs_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_lt(v_i_446_, v_sz_445_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_bs_447_);
return v___x_454_;
}
else
{
lean_object* v_v_455_; lean_object* v___x_456_; lean_object* v_bs_x27_457_; lean_object* v___x_458_; 
v_v_455_ = lean_array_uget(v_bs_447_, v_i_446_);
v___x_456_ = lean_unsigned_to_nat(0u);
v_bs_x27_457_ = lean_array_uset(v_bs_447_, v_i_446_, v___x_456_);
v___x_458_ = l_Lean_Meta_NormCast_countCoes(v_v_455_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_446_, v___x_460_);
v___x_462_ = lean_array_uset(v_bs_x27_457_, v_i_446_, v_a_459_);
v_i_446_ = v___x_461_;
v_bs_447_ = v___x_462_;
goto _start;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_bs_x27_457_);
v_a_464_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_458_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(lean_object* v_upperBound_472_, lean_object* v___x_473_, lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_lt(v_a_475_, v_upperBound_472_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec(v_a_475_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_b_476_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = lean_nat_sub(v___x_473_, v_a_475_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_sub(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = l_Lean_Expr_getRevArg_x21(v_e_474_, v___x_486_);
v___x_488_ = l_Lean_Meta_NormCast_countCoes(v___x_487_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = lean_nat_add(v_b_476_, v_a_489_);
lean_dec(v_a_489_);
lean_dec(v_b_476_);
v___x_491_ = lean_nat_add(v_a_475_, v___x_485_);
lean_dec(v_a_475_);
v_a_475_ = v___x_491_;
v_b_476_ = v___x_490_;
goto _start;
}
else
{
lean_dec(v_b_476_);
lean_dec(v_a_475_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0(lean_object* v_x_493_, lean_object* v_e_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Expr_getAppFn(v_e_494_);
if (lean_obj_tag(v___x_538_) == 4)
{
lean_object* v_declName_539_; lean_object* v___x_540_; 
v_declName_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_declName_539_);
lean_dec_ref_known(v___x_538_, 2);
v___x_540_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_539_, v___y_498_);
lean_dec(v_declName_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
if (lean_obj_tag(v_a_541_) == 1)
{
lean_object* v_val_542_; lean_object* v_numArgs_543_; lean_object* v_coercee_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_val_542_ = lean_ctor_get(v_a_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_a_541_, 1);
v_numArgs_543_ = lean_ctor_get(v_val_542_, 0);
lean_inc(v_numArgs_543_);
v_coercee_544_ = lean_ctor_get(v_val_542_, 1);
lean_inc(v_coercee_544_);
lean_dec(v_val_542_);
v___x_545_ = l_Lean_Expr_getAppNumArgs(v_e_494_);
v___x_546_ = lean_nat_dec_le(v_numArgs_543_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v___x_545_);
lean_dec(v_coercee_544_);
lean_dec(v_numArgs_543_);
goto v___jp_500_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = lean_nat_sub(v___x_545_, v_coercee_544_);
lean_dec(v_coercee_544_);
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_sub(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
v___x_550_ = l_Lean_Expr_getRevArg_x21(v_e_494_, v___x_549_);
v___x_551_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___x_550_, v___y_498_);
lean_dec_ref(v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = lean_nat_add(v_a_552_, v___x_548_);
lean_dec(v_a_552_);
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v___x_545_, v___x_545_, v_e_494_, v_numArgs_543_, v___x_553_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec_ref(v_e_494_);
lean_dec(v___x_545_);
return v___x_554_;
}
else
{
lean_dec(v___x_545_);
lean_dec(v_numArgs_543_);
lean_dec_ref(v_e_494_);
return v___x_551_;
}
}
}
else
{
lean_dec(v_a_541_);
goto v___jp_500_;
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_e_494_);
v_a_555_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_540_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_540_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_dec_ref(v___x_538_);
goto v___jp_500_;
}
v___jp_500_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_NormCast_getSimpArgs(v_e_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; size_t v_sz_503_; size_t v___x_504_; lean_object* v___x_505_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v_sz_503_ = lean_array_size(v_a_502_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_503_, v___x_504_, v_a_502_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_521_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_521_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_521_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_521_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_array_get_size(v_a_506_);
v___x_512_ = lean_nat_dec_lt(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_510_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
size_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_usize_of_nat(v___x_511_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_506_, v___x_504_, v___x_516_, v___x_510_);
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_505_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_505_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_501_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_501_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
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
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0___boxed(lean_object* v_x_563_, lean_object* v_e_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_NormCast_countCoes___lam__0(v_x_563_, v_e_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v_x_563_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes(lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___f_577_; uint8_t v___x_578_; lean_object* v___x_579_; 
v___f_577_ = lean_alloc_closure((void*)(l_Lean_Meta_NormCast_countCoes___lam__0___boxed), 7, 0);
v___x_578_ = 0;
v___x_579_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_571_, v___f_577_, v___x_578_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___boxed(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_NormCast_countCoes(v_e_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg___boxed(lean_object* v_upperBound_587_, lean_object* v___x_588_, lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_587_, v___x_588_, v_e_589_, v_a_590_, v_b_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_e_589_);
lean_dec(v___x_588_);
lean_dec(v_upperBound_587_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0___boxed(lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_bs_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
size_t v_sz_boxed_606_; size_t v_i_boxed_607_; lean_object* v_res_608_; 
v_sz_boxed_606_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_607_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_boxed_606_, v_i_boxed_607_, v_bs_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(lean_object* v_upperBound_609_, lean_object* v___x_610_, lean_object* v_e_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_c_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_609_, v___x_610_, v_e_611_, v_a_614_, v_b_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___boxed(lean_object* v_upperBound_623_, lean_object* v___x_624_, lean_object* v_e_625_, lean_object* v_inst_626_, lean_object* v_R_627_, lean_object* v_a_628_, lean_object* v_b_629_, lean_object* v_c_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(v_upperBound_623_, v___x_624_, v_e_625_, v_inst_626_, v_R_627_, v_a_628_, v_b_629_, v_c_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v_e_625_);
lean_dec(v___x_624_);
lean_dec(v_upperBound_623_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes(lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; 
lean_inc_ref(v_e_637_);
v___x_643_ = l_Lean_Meta_NormCast_countCoes(v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_637_, v_a_641_);
lean_dec_ref(v_e_637_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_nat_sub(v_a_644_, v_a_646_);
lean_dec(v_a_646_);
lean_dec(v_a_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_dec(v_a_644_);
return v___x_645_;
}
}
else
{
lean_dec_ref(v_e_637_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes___boxed(lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_NormCast_countInternalCoes(v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(lean_object* v_type_662_, lean_object* v_k_663_, uint8_t v_cleanupAnnotations_664_, uint8_t v_whnfType_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___f_671_; lean_object* v___x_672_; 
v___f_671_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_671_, 0, v_k_663_);
v___x_672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_662_, v___f_671_, v_cleanupAnnotations_664_, v_whnfType_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_672_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_672_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg___boxed(lean_object* v_type_689_, lean_object* v_k_690_, lean_object* v_cleanupAnnotations_691_, lean_object* v_whnfType_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_698_; uint8_t v_whnfType_boxed_699_; lean_object* v_res_700_; 
v_cleanupAnnotations_boxed_698_ = lean_unbox(v_cleanupAnnotations_691_);
v_whnfType_boxed_699_ = lean_unbox(v_whnfType_692_);
v_res_700_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_689_, v_k_690_, v_cleanupAnnotations_boxed_698_, v_whnfType_boxed_699_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(lean_object* v_00_u03b1_701_, lean_object* v_type_702_, lean_object* v_k_703_, uint8_t v_cleanupAnnotations_704_, uint8_t v_whnfType_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_702_, v_k_703_, v_cleanupAnnotations_704_, v_whnfType_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___boxed(lean_object* v_00_u03b1_712_, lean_object* v_type_713_, lean_object* v_k_714_, lean_object* v_cleanupAnnotations_715_, lean_object* v_whnfType_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_722_; uint8_t v_whnfType_boxed_723_; lean_object* v_res_724_; 
v_cleanupAnnotations_boxed_722_ = lean_unbox(v_cleanupAnnotations_715_);
v_whnfType_boxed_723_ = lean_unbox(v_whnfType_716_);
v_res_724_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(v_00_u03b1_712_, v_type_713_, v_k_714_, v_cleanupAnnotations_boxed_722_, v_whnfType_boxed_723_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(lean_object* v_msgData_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v_env_732_; uint8_t v___x_733_; lean_object* v_env_734_; lean_object* v___x_735_; lean_object* v_toCold_736_; lean_object* v_mctx_737_; lean_object* v_lctx_738_; lean_object* v_options_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_731_ = lean_st_ref_get(v___y_729_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_731_);
v___x_733_ = 0;
v_env_734_ = l_Lean_Environment_setRecordingDeps(v_env_732_, v___x_733_);
v___x_735_ = lean_st_ref_get(v___y_727_);
v_toCold_736_ = lean_ctor_get(v___y_728_, 0);
v_mctx_737_ = lean_ctor_get(v___x_735_, 0);
lean_inc_ref(v_mctx_737_);
lean_dec(v___x_735_);
v_lctx_738_ = lean_ctor_get(v___y_726_, 2);
v_options_739_ = lean_ctor_get(v_toCold_736_, 2);
lean_inc_ref(v_options_739_);
lean_inc_ref(v_lctx_738_);
v___x_740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_740_, 0, v_env_734_);
lean_ctor_set(v___x_740_, 1, v_mctx_737_);
lean_ctor_set(v___x_740_, 2, v_lctx_738_);
lean_ctor_set(v___x_740_, 3, v_options_739_);
v___x_741_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_msgData_725_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0___boxed(lean_object* v_msgData_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msgData_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(lean_object* v_msg_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_ref_756_; lean_object* v___x_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_ref_756_ = lean_ctor_get(v___y_753_, 2);
v___x_757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msg_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
lean_inc(v_ref_756_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_ref_756_);
lean_ctor_set(v___x_762_, 1, v_a_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 1);
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg___boxed(lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__0));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__2));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__4));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__5, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5);
v___x_784_ = l_Lean_MessageData_note(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__7));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__13));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0(lean_object* v_x_797_, lean_object* v_ty_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___x_814_; 
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
v___x_814_ = lean_whnf(v_ty_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_925_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__10));
v___x_926_ = lean_unsigned_to_nat(3u);
v___x_927_ = l_Lean_Expr_isAppOfArity(v_a_815_, v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__12));
v___x_929_ = lean_unsigned_to_nat(2u);
v___x_930_ = l_Lean_Expr_isAppOfArity(v_a_815_, v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v___x_931_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__14, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14);
v___x_932_ = l_Lean_indentExpr(v_a_815_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_933_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_943_ = l_Lean_Expr_getAppNumArgs(v_a_815_);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_sub(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
lean_inc(v___x_945_);
v___x_946_ = l_Lean_Expr_getRevArg_x21(v_a_815_, v___x_945_);
v___x_947_ = lean_nat_sub(v___x_945_, v___x_944_);
lean_dec(v___x_945_);
v___x_948_ = l_Lean_Expr_getRevArg_x21(v_a_815_, v___x_947_);
v_fst_893_ = v___x_946_;
v_snd_894_ = v___x_948_;
v___y_895_ = v___y_799_;
v___y_896_ = v___y_800_;
v___y_897_ = v___y_801_;
v___y_898_ = v___y_802_;
goto v___jp_892_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = l_Lean_Expr_getAppNumArgs(v_a_815_);
v___x_951_ = lean_nat_sub(v___x_950_, v___x_949_);
v___x_952_ = lean_nat_sub(v___x_951_, v___x_949_);
lean_dec(v___x_951_);
v___x_953_ = l_Lean_Expr_getRevArg_x21(v_a_815_, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(2u);
v___x_955_ = lean_nat_sub(v___x_950_, v___x_954_);
lean_dec(v___x_950_);
v___x_956_ = lean_nat_sub(v___x_955_, v___x_949_);
lean_dec(v___x_955_);
v___x_957_ = l_Lean_Expr_getRevArg_x21(v_a_815_, v___x_956_);
v_fst_893_ = v___x_953_;
v_snd_894_ = v___x_957_;
v___y_895_ = v___y_799_;
v___y_896_ = v___y_800_;
v___y_897_ = v___y_801_;
v___y_898_ = v___y_802_;
goto v___jp_892_;
}
v___jp_816_:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_819_, v___y_823_);
lean_dec_ref(v___y_819_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_818_, v___y_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
lean_inc_ref(v___y_818_);
v___x_828_ = l_Lean_Meta_NormCast_countInternalCoes(v___y_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_867_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_867_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_867_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_867_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_dec_eq(v_a_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_dec_eq(v_a_825_, v___x_835_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
lean_dec(v_a_829_);
lean_dec_ref(v___y_818_);
v___x_837_ = lean_nat_dec_lt(v_a_827_, v_a_825_);
lean_dec(v_a_825_);
lean_dec(v_a_827_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_831_);
v___x_838_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__1, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1);
v___x_839_ = l_Lean_indentExpr(v_a_815_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_inc_ref(v___y_817_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___y_817_);
v___x_842_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_841_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec(v_a_815_);
v___x_843_ = 2;
v___x_844_ = lean_box(v___x_843_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_844_);
v___x_846_ = v___x_831_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
uint8_t v___x_848_; 
lean_del_object(v___x_831_);
lean_dec(v_a_825_);
lean_dec(v_a_815_);
v___x_848_ = lean_nat_dec_eq(v_a_827_, v___x_833_);
lean_dec(v_a_827_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_829_);
v___x_849_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__3, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3);
v___x_850_ = l_Lean_indentExpr(v___y_818_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
lean_inc_ref(v___y_817_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v___y_817_);
v___x_853_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_852_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_dec_ref(v___y_818_);
v___y_805_ = v___x_833_;
v___y_806_ = v_a_829_;
goto v___jp_804_;
}
}
}
else
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
lean_dec(v_a_829_);
lean_dec(v_a_827_);
lean_dec(v_a_825_);
lean_dec_ref(v___y_818_);
lean_dec(v_a_815_);
v___x_862_ = 0;
v___x_863_ = lean_box(v___x_862_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_863_);
v___x_865_ = v___x_831_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_827_);
lean_dec(v_a_825_);
lean_dec_ref(v___y_818_);
lean_dec(v_a_815_);
v_a_868_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_828_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_828_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_825_);
lean_dec_ref(v___y_818_);
lean_dec(v_a_815_);
v_a_876_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_826_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_826_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___y_818_);
lean_dec(v_a_815_);
v_a_884_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_824_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_824_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
v___jp_892_:
{
lean_object* v___x_899_; 
lean_inc_ref(v_fst_893_);
v___x_899_ = l_Lean_Meta_NormCast_countCoes(v_fst_893_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__6, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_nat_dec_eq(v_a_900_, v___x_902_);
lean_dec(v_a_900_);
if (v___x_903_ == 0)
{
v___y_817_ = v___x_901_;
v___y_818_ = v_snd_894_;
v___y_819_ = v_fst_893_;
v___y_820_ = v___y_895_;
v___y_821_ = v___y_896_;
v___y_822_ = v___y_897_;
v___y_823_ = v___y_898_;
goto v___jp_816_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_snd_894_);
lean_dec(v_a_815_);
v___x_904_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__8, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8);
v___x_905_ = l_Lean_indentExpr(v_fst_893_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_901_);
v___x_908_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_907_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_snd_894_);
lean_dec_ref(v_fst_893_);
lean_dec(v_a_815_);
v_a_917_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_899_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_899_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_814_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_814_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
v___jp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_eq(v___y_806_, v___y_805_);
lean_dec(v___y_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = 1;
v___x_809_ = lean_box(v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
else
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 2;
v___x_812_ = lean_box(v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___boxed(lean_object* v_x_966_, lean_object* v_ty_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Meta_NormCast_classifyType___lam__0(v_x_966_, v_ty_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_x_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType(lean_object* v_ty_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___f_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v___f_981_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___closed__0));
v___x_982_ = 0;
v___x_983_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_ty_975_, v___f_981_, v___x_982_, v___x_982_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___boxed(lean_object* v_ty_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_NormCast_classifyType(v_ty_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(lean_object* v_00_u03b1_991_, lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___boxed(lean_object* v_00_u03b1_999_, lean_object* v_msg_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(v_00_u03b1_999_, v_msg_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1024_ = l_Lean_Meta_registerSimpAttr(v___x_1021_, v___x_1022_, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2____boxed(lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = l_Lean_Meta_instInhabitedSimpEntry_default;
v___x_1028_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0);
v___x_1030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension(void){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default;
return v___x_1032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1044_ = l_Lean_Name_append(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1050_ = l_Lean_Name_append(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1056_ = l_Lean_Name_append(v___x_1055_, v___x_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1059_ = l_Lean_Meta_mkSimpExt(v___x_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1062_ = l_Lean_Meta_mkSimpExt(v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1065_ = l_Lean_Meta_mkSimpExt(v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1074_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1070_, 0, v_a_1060_);
lean_ctor_set(v___x_1070_, 1, v_a_1063_);
lean_ctor_set(v___x_1070_, 2, v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
v_a_1075_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1065_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1065_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1060_);
v_a_1083_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1062_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1062_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1059_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1059_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2____boxed(lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim(lean_object* v_decl_1101_, uint8_t v_kind_1102_, lean_object* v_prio_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_up_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1110_ = lean_ctor_get(v___x_1109_, 0);
v___x_1111_ = 1;
v___x_1112_ = 0;
lean_inc_ref(v_up_1110_);
v___x_1113_ = l_Lean_Meta_addSimpTheorem(v_up_1110_, v_decl_1101_, v___x_1111_, v___x_1112_, v_kind_1102_, v_prio_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim___boxed(lean_object* v_decl_1114_, lean_object* v_kind_1115_, lean_object* v_prio_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
uint8_t v_kind_boxed_1122_; lean_object* v_res_1123_; 
v_kind_boxed_1122_ = lean_unbox(v_kind_1115_);
v_res_1123_ = l_Lean_Meta_NormCast_addElim(v_decl_1114_, v_kind_boxed_1122_, v_prio_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove(lean_object* v_decl_1124_, uint8_t v_kind_1125_, lean_object* v_prio_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1132_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1133_ = 1;
v___x_1134_ = 0;
lean_inc(v_prio_1126_);
lean_inc(v_decl_1124_);
v___x_1135_ = l_Lean_Meta_addSimpTheorem(v___x_1132_, v_decl_1124_, v___x_1133_, v___x_1134_, v_kind_1125_, v_prio_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v_up_1137_; lean_object* v_down_1138_; lean_object* v___x_1139_; 
lean_dec_ref_known(v___x_1135_, 1);
v___x_1136_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1137_ = lean_ctor_get(v___x_1136_, 0);
v_down_1138_ = lean_ctor_get(v___x_1136_, 1);
lean_inc(v_prio_1126_);
lean_inc(v_decl_1124_);
lean_inc_ref(v_up_1137_);
v___x_1139_ = l_Lean_Meta_addSimpTheorem(v_up_1137_, v_decl_1124_, v___x_1133_, v___x_1133_, v_kind_1125_, v_prio_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref_known(v___x_1139_, 1);
lean_inc_ref(v_down_1138_);
v___x_1140_ = l_Lean_Meta_addSimpTheorem(v_down_1138_, v_decl_1124_, v___x_1133_, v___x_1134_, v_kind_1125_, v_prio_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1140_;
}
else
{
lean_dec(v_prio_1126_);
lean_dec(v_decl_1124_);
return v___x_1139_;
}
}
else
{
lean_dec(v_prio_1126_);
lean_dec(v_decl_1124_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove___boxed(lean_object* v_decl_1141_, lean_object* v_kind_1142_, lean_object* v_prio_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v_kind_boxed_1149_; lean_object* v_res_1150_; 
v_kind_boxed_1149_ = lean_unbox(v_kind_1142_);
v_res_1150_ = l_Lean_Meta_NormCast_addMove(v_decl_1141_, v_kind_boxed_1149_, v_prio_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash(lean_object* v_decl_1151_, uint8_t v_kind_1152_, lean_object* v_prio_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1160_ = 1;
v___x_1161_ = 0;
lean_inc(v_prio_1153_);
lean_inc(v_decl_1151_);
v___x_1162_ = l_Lean_Meta_addSimpTheorem(v___x_1159_, v_decl_1151_, v___x_1160_, v___x_1161_, v_kind_1152_, v_prio_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v___x_1163_; lean_object* v_down_1164_; lean_object* v_squash_1165_; lean_object* v___x_1166_; 
lean_dec_ref_known(v___x_1162_, 1);
v___x_1163_ = l_Lean_Meta_NormCast_normCastExt;
v_down_1164_ = lean_ctor_get(v___x_1163_, 1);
v_squash_1165_ = lean_ctor_get(v___x_1163_, 2);
lean_inc(v_prio_1153_);
lean_inc(v_decl_1151_);
lean_inc_ref(v_squash_1165_);
v___x_1166_ = l_Lean_Meta_addSimpTheorem(v_squash_1165_, v_decl_1151_, v___x_1160_, v___x_1161_, v_kind_1152_, v_prio_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1167_; 
lean_dec_ref_known(v___x_1166_, 1);
lean_inc_ref(v_down_1164_);
v___x_1167_ = l_Lean_Meta_addSimpTheorem(v_down_1164_, v_decl_1151_, v___x_1160_, v___x_1161_, v_kind_1152_, v_prio_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1167_;
}
else
{
lean_dec(v_prio_1153_);
lean_dec(v_decl_1151_);
return v___x_1166_;
}
}
else
{
lean_dec(v_prio_1153_);
lean_dec(v_decl_1151_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash___boxed(lean_object* v_decl_1168_, lean_object* v_kind_1169_, lean_object* v_prio_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
uint8_t v_kind_boxed_1176_; lean_object* v_res_1177_; 
v_kind_boxed_1176_ = lean_unbox(v_kind_1169_);
v_res_1177_ = l_Lean_Meta_NormCast_addSquash(v_decl_1168_, v_kind_boxed_1176_, v_prio_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
lean_ctor_set(v___x_1184_, 4, v___x_1182_);
lean_ctor_set(v___x_1184_, 5, v___x_1182_);
lean_ctor_set(v___x_1184_, 6, v___x_1182_);
lean_ctor_set(v___x_1184_, 7, v___x_1182_);
lean_ctor_set(v___x_1184_, 8, v___x_1182_);
lean_ctor_set(v___x_1184_, 9, v___x_1182_);
lean_ctor_set(v___x_1184_, 10, v___x_1182_);
lean_ctor_set(v___x_1184_, 11, v___x_1181_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(32u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1188_ = ((size_t)5ULL);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_unsigned_to_nat(32u);
v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
v___x_1192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1193_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v___x_1189_);
lean_ctor_set(v___x_1193_, 3, v___x_1189_);
lean_ctor_set_usize(v___x_1193_, 4, v___x_1188_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(1);
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1196_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
lean_ctor_set(v___x_1197_, 2, v___x_1194_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1200_ = l_Lean_stringToMessageData(v___x_1199_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1203_ = l_Lean_stringToMessageData(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1219_, lean_object* v_declHint_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_env_1225_; uint8_t v___x_1226_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_st_ref_get(v___y_1221_);
v_env_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_ref(v_env_1225_);
lean_dec(v___x_1224_);
v___x_1226_ = l_Lean_Name_isAnonymous(v_declHint_1220_);
if (v___x_1226_ == 0)
{
uint8_t v_isExporting_1227_; 
v_isExporting_1227_ = lean_ctor_get_uint8(v_env_1225_, sizeof(void*)*13);
if (v_isExporting_1227_ == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_env_1225_);
lean_dec(v_declHint_1220_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_msg_1219_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
lean_inc_ref(v_env_1225_);
v___x_1229_ = l_Lean_Environment_setExporting(v_env_1225_, v___x_1226_);
lean_inc(v_declHint_1220_);
lean_inc_ref(v___x_1229_);
v___x_1230_ = l_Lean_Environment_contains(v___x_1229_, v_declHint_1220_, v_isExporting_1227_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_env_1225_);
lean_dec(v_declHint_1220_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_msg_1219_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_c_1237_; lean_object* v___x_1238_; 
v___x_1232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1234_ = l_Lean_Options_empty;
v___x_1235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1229_);
lean_ctor_set(v___x_1235_, 1, v___x_1232_);
lean_ctor_set(v___x_1235_, 2, v___x_1233_);
lean_ctor_set(v___x_1235_, 3, v___x_1234_);
lean_inc(v_declHint_1220_);
v___x_1236_ = l_Lean_MessageData_ofConstName(v_declHint_1220_, v___x_1226_);
v_c_1237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1237_, 0, v___x_1235_);
lean_ctor_set(v_c_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1225_, v_declHint_1220_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_env_1225_);
lean_dec(v_declHint_1220_);
v___x_1239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_c_1237_);
v___x_1241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_MessageData_note(v___x_1242_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_msg_1219_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1280_; 
v_val_1246_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1248_ = v___x_1238_;
v_isShared_1249_ = v_isSharedCheck_1280_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_dec(v___x_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1280_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v_moduleNames_1251_; lean_object* v_mod_1252_; uint8_t v___x_1253_; 
v___x_1250_ = l_Lean_Environment_header(v_env_1225_);
lean_dec_ref(v_env_1225_);
v_moduleNames_1251_ = lean_ctor_get(v___x_1250_, 4);
lean_inc_ref(v_moduleNames_1251_);
lean_dec_ref(v___x_1250_);
v_mod_1252_ = lean_array_get(v___x_1223_, v_moduleNames_1251_, v_val_1246_);
lean_dec(v_val_1246_);
lean_dec_ref(v_moduleNames_1251_);
v___x_1253_ = l_Lean_isPrivateName(v_declHint_1220_);
lean_dec(v_declHint_1220_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_c_1237_);
v___x_1256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Lean_MessageData_ofName(v_mod_1252_);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_MessageData_note(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_msg_1219_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1263_);
v___x_1265_ = v___x_1248_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v_c_1237_);
v___x_1269_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_MessageData_ofName(v_mod_1252_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_MessageData_note(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_msg_1219_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1276_);
v___x_1278_ = v___x_1248_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v_env_1225_);
lean_dec(v_declHint_1220_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_msg_1219_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1282_, lean_object* v_declHint_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1282_, v_declHint_1283_, v___y_1284_);
lean_dec(v___y_1284_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1287_, lean_object* v_declHint_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1304_; 
v___x_1294_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1287_, v_declHint_1288_, v___y_1292_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = l_Lean_unknownIdentifierMessageTag;
v___x_1300_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_a_1295_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1305_, lean_object* v_declHint_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1305_, v_declHint_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1313_, lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_toCold_1320_; lean_object* v_currRecDepth_1321_; lean_object* v_ref_1322_; uint16_t v_optionFlags_1323_; uint8_t v_suppressElabErrors_1324_; uint8_t v_isRecordingDeps_1325_; lean_object* v_ref_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_toCold_1320_ = lean_ctor_get(v___y_1317_, 0);
v_currRecDepth_1321_ = lean_ctor_get(v___y_1317_, 1);
v_ref_1322_ = lean_ctor_get(v___y_1317_, 2);
v_optionFlags_1323_ = lean_ctor_get_uint16(v___y_1317_, sizeof(void*)*3);
v_suppressElabErrors_1324_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1325_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 3);
v_ref_1326_ = l_Lean_replaceRef(v_ref_1313_, v_ref_1322_);
lean_inc(v_currRecDepth_1321_);
lean_inc_ref(v_toCold_1320_);
v___x_1327_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1327_, 0, v_toCold_1320_);
lean_ctor_set(v___x_1327_, 1, v_currRecDepth_1321_);
lean_ctor_set(v___x_1327_, 2, v_ref_1326_);
lean_ctor_set_uint16(v___x_1327_, sizeof(void*)*3, v_optionFlags_1323_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*3 + 2, v_suppressElabErrors_1324_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*3 + 3, v_isRecordingDeps_1325_);
v___x_1328_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_1314_, v___y_1315_, v___y_1316_, v___x_1327_, v___y_1318_);
lean_dec_ref_known(v___x_1327_, 3);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1329_, v_msg_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v_ref_1329_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1337_, lean_object* v_msg_1338_, lean_object* v_declHint_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_a_1346_; lean_object* v___x_1347_; 
v___x_1345_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1338_, v_declHint_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1337_, v_a_1346_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1348_, lean_object* v_msg_1349_, lean_object* v_declHint_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1348_, v_msg_1349_, v_declHint_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v_ref_1348_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1363_, lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1371_ = 0;
lean_inc(v_constName_1364_);
v___x_1372_ = l_Lean_MessageData_ofConstName(v_constName_1364_, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1363_, v___x_1375_, v_constName_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1377_, lean_object* v_constName_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1377_, v_constName_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_ref_1377_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(lean_object* v_constName_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_ref_1391_; lean_object* v___x_1392_; 
v_ref_1391_ = lean_ctor_get(v___y_1388_, 2);
v___x_1392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1391_, v_constName_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(lean_object* v_constName_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_env_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = lean_st_ref_get(v___y_1404_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = 0;
lean_inc(v_constName_1400_);
v___x_1409_ = l_Lean_Environment_findConstVal_x3f(v_env_1407_, v_constName_1400_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1410_;
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_constName_1400_);
v_val_1411_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1409_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_val_1411_);
lean_dec(v___x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_val_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0___boxed(lean_object* v_constName_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_constName_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer(lean_object* v_decl_1426_, uint8_t v_kind_1427_, lean_object* v_prio_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1434_; 
lean_inc(v_decl_1426_);
v___x_1434_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_decl_1426_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_type_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v_type_1436_ = lean_ctor_get(v_a_1435_, 2);
lean_inc_ref(v_type_1436_);
lean_dec(v_a_1435_);
v___x_1437_ = l_Lean_Meta_NormCast_classifyType(v_type_1436_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_unbox(v_a_1438_);
lean_dec(v_a_1438_);
switch(v___x_1439_)
{
case 0:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_NormCast_addElim(v_decl_1426_, v_kind_1427_, v_prio_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1440_;
}
case 1:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_NormCast_addMove(v_decl_1426_, v_kind_1427_, v_prio_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1441_;
}
default: 
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Meta_NormCast_addSquash(v_decl_1426_, v_kind_1427_, v_prio_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_prio_1428_);
lean_dec(v_decl_1426_);
v_a_1443_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1437_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1437_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_prio_1428_);
lean_dec(v_decl_1426_);
v_a_1451_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1434_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1434_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer___boxed(lean_object* v_decl_1459_, lean_object* v_kind_1460_, lean_object* v_prio_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
uint8_t v_kind_boxed_1467_; lean_object* v_res_1468_; 
v_kind_boxed_1467_ = lean_unbox(v_kind_1460_);
v_res_1468_ = l_Lean_Meta_NormCast_addInfer(v_decl_1459_, v_kind_boxed_1467_, v_prio_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(lean_object* v_00_u03b1_1469_, lean_object* v_constName_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_constName_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(v_00_u03b1_1477_, v_constName_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1485_, lean_object* v_ref_1486_, lean_object* v_constName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1486_, v_constName_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(v_00_u03b1_1494_, v_ref_1495_, v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_ref_1495_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1503_, lean_object* v_ref_1504_, lean_object* v_msg_1505_, lean_object* v_declHint_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1504_, v_msg_1505_, v_declHint_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_ref_1514_, lean_object* v_msg_1515_, lean_object* v_declHint_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1513_, v_ref_1514_, v_msg_1515_, v_declHint_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v_ref_1514_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1523_, lean_object* v_declHint_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1523_, v_declHint_1524_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1531_, lean_object* v_declHint_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1531_, v_declHint_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1539_, lean_object* v_ref_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1540_, v_msg_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1548_, v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v_ref_1549_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___f_1564_; lean_object* v___x_957__overap_1565_; lean_object* v___x_1566_; 
v___f_1564_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0));
v___x_957__overap_1565_ = lean_panic_fn_borrowed(v___f_1564_, v_msg_1558_);
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
v___x_1566_ = lean_apply_5(v___x_957__overap_1565_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, lean_box(0));
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___boxed(lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v_msg_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1580_ = lean_unsigned_to_nat(11u);
v___x_1581_ = lean_unsigned_to_nat(165u);
v___x_1582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1584_ = l_mkPanicMessageWithDecl(v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_, v___x_1579_);
return v___x_1584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1586_ = lean_unsigned_to_nat(71u);
v___x_1587_ = lean_unsigned_to_nat(158u);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1590_ = l_mkPanicMessageWithDecl(v___x_1589_, v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v_decl_1591_, uint8_t v_kind_1592_, lean_object* v_stx_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_x_1597_, lean_object* v_label_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = l_Lean_Syntax_getArg(v_stx_1593_, v___x_1594_);
v___x_1633_ = l_Lean_Syntax_isNone(v___x_1632_);
if (v___x_1633_ == 0)
{
uint8_t v___x_1634_; 
lean_inc(v___x_1632_);
v___x_1634_ = l_Lean_Syntax_matchesNull(v___x_1632_, v___x_1595_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v___x_1632_);
lean_dec(v_decl_1591_);
v___x_1635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1636_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1635_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
return v___x_1636_;
}
else
{
lean_object* v_prio_1637_; lean_object* v___x_1638_; 
v_prio_1637_ = l_Lean_Syntax_getArg(v___x_1632_, v___x_1596_);
lean_dec(v___x_1632_);
v___x_1638_ = l_Lean_Syntax_isNatLit_x3f(v_prio_1637_);
lean_dec(v_prio_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
v___y_1627_ = v___y_1602_;
v___y_1628_ = v___y_1601_;
v___y_1629_ = v___y_1599_;
v___y_1630_ = v___y_1600_;
goto v___jp_1626_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1605_ = v___y_1602_;
v___y_1606_ = v___y_1601_;
v___y_1607_ = v___y_1599_;
v___y_1608_ = v___y_1600_;
v___y_1609_ = v_val_1639_;
goto v___jp_1604_;
}
}
}
else
{
lean_dec(v___x_1632_);
v___y_1627_ = v___y_1602_;
v___y_1628_ = v___y_1601_;
v___y_1629_ = v___y_1599_;
v___y_1630_ = v___y_1600_;
goto v___jp_1626_;
}
v___jp_1604_:
{
if (lean_obj_tag(v_label_1598_) == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_NormCast_addInfer(v_decl_1591_, v_kind_1592_, v___y_1609_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1610_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1612_; 
v_val_1611_ = lean_ctor_get(v_label_1598_, 0);
v___x_1612_ = l_Lean_Syntax_isStrLit_x3f(v_val_1611_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_NormCast_addInfer(v_decl_1591_, v_kind_1592_, v___y_1609_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1613_;
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_val_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1616_ = lean_string_dec_eq(v_val_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1618_ = lean_string_dec_eq(v_val_1614_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1620_ = lean_string_dec_eq(v_val_1614_, v___x_1619_);
lean_dec(v_val_1614_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v___y_1609_);
lean_dec(v_decl_1591_);
v___x_1621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1622_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1621_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_NormCast_addSquash(v_decl_1591_, v_kind_1592_, v___y_1609_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1623_;
}
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_val_1614_);
v___x_1624_ = l_Lean_Meta_NormCast_addMove(v_decl_1591_, v_kind_1592_, v___y_1609_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1624_;
}
}
else
{
lean_object* v___x_1625_; 
lean_dec(v_val_1614_);
v___x_1625_ = l_Lean_Meta_NormCast_addElim(v_decl_1591_, v_kind_1592_, v___y_1609_, v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_);
return v___x_1625_;
}
}
}
}
v___jp_1626_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_unsigned_to_nat(1000u);
v___y_1605_ = v___y_1627_;
v___y_1606_ = v___y_1628_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___y_1630_;
v___y_1609_ = v___x_1631_;
goto v___jp_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_decl_1640_, lean_object* v_kind_1641_, lean_object* v_stx_1642_, lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_x_1646_, lean_object* v_label_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_kind_boxed_1653_; lean_object* v_res_1654_; 
v_kind_boxed_1653_ = lean_unbox(v_kind_1641_);
v_res_1654_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1640_, v_kind_boxed_1653_, v_stx_1642_, v___x_1643_, v___x_1644_, v___x_1645_, v_x_1646_, v_label_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v_label_1647_);
lean_dec(v___x_1645_);
lean_dec(v___x_1644_);
lean_dec(v___x_1643_);
lean_dec(v_stx_1642_);
return v_res_1654_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1663_; uint64_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1663_);
return v___x_1664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set_uint64(v___x_1667_, sizeof(void*)*1, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1671_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
lean_ctor_set(v___x_1671_, 3, v___x_1670_);
lean_ctor_set(v___x_1671_, 4, v___x_1670_);
lean_ctor_set(v___x_1671_, 5, v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
lean_ctor_set(v___x_1673_, 2, v___x_1672_);
lean_ctor_set(v___x_1673_, 3, v___x_1672_);
lean_ctor_set(v___x_1673_, 4, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1675_, lean_object* v___x_1676_, lean_object* v___x_1677_, lean_object* v___x_1678_, lean_object* v___x_1679_, lean_object* v_decl_1680_, lean_object* v_stx_1681_, uint8_t v_kind_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; uint8_t v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; size_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___y_1711_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
lean_inc_ref(v___x_1675_);
v___x_1688_ = l_Lean_Name_mkStr4(v___x_1675_, v___x_1686_, v___x_1687_, v___x_1676_);
lean_inc(v_stx_1681_);
v___x_1689_ = l_Lean_Syntax_isOfKind(v_stx_1681_, v___x_1688_);
lean_dec(v___x_1688_);
v___x_1690_ = 1;
v___x_1691_ = 0;
v___x_1692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1694_ = lean_unsigned_to_nat(32u);
v___x_1695_ = lean_mk_empty_array_with_capacity(v___x_1694_);
v___x_1696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1697_ = ((size_t)5ULL);
lean_inc_n(v___x_1677_, 7);
v___x_1698_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1695_);
lean_ctor_set(v___x_1698_, 2, v___x_1677_);
lean_ctor_set(v___x_1698_, 3, v___x_1677_);
lean_ctor_set_usize(v___x_1698_, 4, v___x_1697_);
v___x_1699_ = lean_box(1);
lean_inc_ref(v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1693_);
lean_ctor_set(v___x_1700_, 1, v___x_1698_);
lean_ctor_set(v___x_1700_, 2, v___x_1699_);
v___x_1701_ = lean_mk_empty_array_with_capacity(v___x_1677_);
v___x_1702_ = lean_box(0);
lean_inc(v___x_1678_);
v___x_1703_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1703_, 0, v___x_1692_);
lean_ctor_set(v___x_1703_, 1, v___x_1678_);
lean_ctor_set(v___x_1703_, 2, v___x_1700_);
lean_ctor_set(v___x_1703_, 3, v___x_1701_);
lean_ctor_set(v___x_1703_, 4, v___x_1702_);
lean_ctor_set(v___x_1703_, 5, v___x_1677_);
lean_ctor_set(v___x_1703_, 6, v___x_1702_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*7, v___x_1691_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*7 + 1, v___x_1691_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*7 + 2, v___x_1691_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*7 + 3, v___x_1690_);
v___x_1704_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1705_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1677_);
lean_ctor_set(v___x_1705_, 1, v___x_1677_);
lean_ctor_set(v___x_1705_, 2, v___x_1677_);
lean_ctor_set(v___x_1705_, 3, v___x_1677_);
lean_ctor_set(v___x_1705_, 4, v___x_1693_);
lean_ctor_set(v___x_1705_, 5, v___x_1693_);
lean_ctor_set(v___x_1705_, 6, v___x_1693_);
lean_ctor_set(v___x_1705_, 7, v___x_1693_);
lean_ctor_set(v___x_1705_, 8, v___x_1693_);
lean_ctor_set(v___x_1705_, 9, v___x_1693_);
lean_ctor_set(v___x_1705_, 10, v___x_1693_);
lean_ctor_set(v___x_1705_, 11, v___x_1704_);
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1705_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1678_);
lean_ctor_set(v___x_1708_, 3, v___x_1698_);
lean_ctor_set(v___x_1708_, 4, v___x_1707_);
v___x_1709_ = lean_st_mk_ref(v___x_1708_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_stx_1681_);
lean_dec(v_decl_1680_);
lean_dec(v___x_1677_);
lean_dec_ref(v___x_1675_);
v___x_1721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1722_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1721_, v___x_1703_, v___x_1709_, v___y_1683_, v___y_1684_);
lean_dec_ref_known(v___x_1703_, 7);
v___y_1711_ = v___x_1722_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = l_Lean_Syntax_getArg(v_stx_1681_, v___x_1723_);
v___x_1725_ = l_Lean_Syntax_isNone(v___x_1724_);
if (v___x_1725_ == 0)
{
uint8_t v___x_1726_; 
lean_inc(v___x_1724_);
v___x_1726_ = l_Lean_Syntax_matchesNull(v___x_1724_, v___x_1723_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec(v___x_1724_);
lean_dec(v_stx_1681_);
lean_dec(v_decl_1680_);
lean_dec(v___x_1677_);
lean_dec_ref(v___x_1675_);
v___x_1727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1728_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1727_, v___x_1703_, v___x_1709_, v___y_1683_, v___y_1684_);
lean_dec_ref_known(v___x_1703_, 7);
v___y_1711_ = v___x_1728_;
goto v___jp_1710_;
}
else
{
lean_object* v_label_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_label_1729_ = l_Lean_Syntax_getArg(v___x_1724_, v___x_1677_);
lean_dec(v___x_1724_);
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1731_ = l_Lean_Name_mkStr4(v___x_1675_, v___x_1686_, v___x_1687_, v___x_1730_);
lean_inc(v_label_1729_);
v___x_1732_ = l_Lean_Syntax_isOfKind(v_label_1729_, v___x_1731_);
lean_dec(v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v_label_1729_);
lean_dec(v_stx_1681_);
lean_dec(v_decl_1680_);
lean_dec(v___x_1677_);
v___x_1733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1734_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1733_, v___x_1703_, v___x_1709_, v___y_1683_, v___y_1684_);
lean_dec_ref_known(v___x_1703_, 7);
v___y_1711_ = v___x_1734_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_label_1729_);
v___x_1737_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1680_, v_kind_1682_, v_stx_1681_, v___x_1679_, v___x_1723_, v___x_1677_, v___x_1735_, v___x_1736_, v___x_1703_, v___x_1709_, v___y_1683_, v___y_1684_);
lean_dec_ref_known(v___x_1703_, 7);
lean_dec_ref_known(v___x_1736_, 1);
lean_dec(v___x_1677_);
lean_dec(v_stx_1681_);
v___y_1711_ = v___x_1737_;
goto v___jp_1710_;
}
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1724_);
lean_dec_ref(v___x_1675_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1680_, v_kind_1682_, v_stx_1681_, v___x_1679_, v___x_1723_, v___x_1677_, v___x_1738_, v___x_1702_, v___x_1703_, v___x_1709_, v___y_1683_, v___y_1684_);
lean_dec_ref_known(v___x_1703_, 7);
lean_dec(v___x_1677_);
lean_dec(v_stx_1681_);
v___y_1711_ = v___x_1739_;
goto v___jp_1710_;
}
}
v___jp_1710_:
{
if (lean_obj_tag(v___y_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_a_1712_ = lean_ctor_get(v___y_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___y_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v___y_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___y_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_st_ref_get(v___x_1709_);
lean_dec(v___x_1709_);
lean_dec(v___x_1716_);
if (v_isShared_1715_ == 0)
{
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_dec(v___x_1709_);
return v___y_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1740_, lean_object* v___x_1741_, lean_object* v___x_1742_, lean_object* v___x_1743_, lean_object* v___x_1744_, lean_object* v_decl_1745_, lean_object* v_stx_1746_, lean_object* v_kind_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v_kind_boxed_1751_; lean_object* v_res_1752_; 
v_kind_boxed_1751_ = lean_unbox(v_kind_1747_);
v_res_1752_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1740_, v___x_1741_, v___x_1742_, v___x_1743_, v___x_1744_, v_decl_1745_, v_stx_1746_, v_kind_boxed_1751_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___x_1744_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v_toCold_1758_; lean_object* v_env_1759_; lean_object* v_options_1760_; uint8_t v___x_1761_; lean_object* v_env_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1757_ = lean_st_ref_get(v___y_1755_);
v_toCold_1758_ = lean_ctor_get(v___y_1754_, 0);
v_env_1759_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_ref(v_env_1759_);
lean_dec(v___x_1757_);
v_options_1760_ = lean_ctor_get(v_toCold_1758_, 2);
v___x_1761_ = 0;
v_env_1762_ = l_Lean_Environment_setRecordingDeps(v_env_1759_, v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1764_ = lean_unsigned_to_nat(32u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
lean_dec_ref(v___x_1765_);
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_1760_);
v___x_1767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1767_, 0, v_env_1762_);
lean_ctor_set(v___x_1767_, 1, v___x_1763_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
lean_ctor_set(v___x_1767_, 3, v_options_1760_);
v___x_1768_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v_msgData_1753_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msgData_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_ref_1779_; lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1789_; 
v_ref_1779_ = lean_ctor_get(v___y_1776_, 2);
v___x_1780_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msg_1775_, v___y_1776_, v___y_1777_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_inc(v_ref_1779_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_ref_1779_);
lean_ctor_set(v___x_1785_, 1, v_a_1781_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 1);
lean_ctor_set(v___x_1783_, 0, v___x_1785_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1801_, lean_object* v_decl_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1807_ = l_Lean_MessageData_ofName(v___x_1801_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v___x_1810_, v___y_1803_, v___y_1804_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1812_, lean_object* v_decl_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1812_, v_decl_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v_decl_1813_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1904_ = l_Lean_registerBuiltinAttribute(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1907_, lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_msg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(v_00_u03b1_1913_, v_msg_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1918_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CoeAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_NormCast_instInhabitedLabel_default = _init_l_Lean_Meta_NormCast_instInhabitedLabel_default();
l_Lean_Meta_NormCast_instInhabitedLabel = _init_l_Lean_Meta_NormCast_instInhabitedLabel();
res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_NormCast_pushCastExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_NormCast_pushCastExt);
lean_dec_ref(res);
l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default = _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default();
lean_mark_persistent(l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default);
l_Lean_Meta_NormCast_instInhabitedNormCastExtension = _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension();
lean_mark_persistent(l_Lean_Meta_NormCast_instInhabitedNormCastExtension);
res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_NormCast_normCastExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_NormCast_normCastExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_CoeAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CoeAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_NormCast(builtin);
}
#ifdef __cplusplus
}
#endif
