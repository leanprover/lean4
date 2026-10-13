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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27;
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
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Expr_getAppFn(v_e_494_);
if (lean_obj_tag(v___x_547_) == 4)
{
lean_object* v_declName_548_; lean_object* v___x_549_; 
v_declName_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_declName_548_);
lean_dec_ref_known(v___x_547_, 2);
v___x_549_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_548_, v___y_498_);
lean_dec(v_declName_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
if (lean_obj_tag(v_a_550_) == 1)
{
lean_object* v_val_551_; lean_object* v_numArgs_552_; lean_object* v_coercee_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_val_551_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_a_550_, 1);
v_numArgs_552_ = lean_ctor_get(v_val_551_, 0);
lean_inc(v_numArgs_552_);
v_coercee_553_ = lean_ctor_get(v_val_551_, 1);
lean_inc(v_coercee_553_);
lean_dec(v_val_551_);
v___x_554_ = l_Lean_Expr_getAppNumArgs(v_e_494_);
v___x_555_ = lean_nat_dec_le(v_numArgs_552_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v___x_554_);
lean_dec(v_coercee_553_);
lean_dec(v_numArgs_552_);
goto v___jp_500_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = lean_nat_sub(v___x_554_, v_coercee_553_);
lean_dec(v_coercee_553_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v___x_559_ = l_Lean_Expr_getRevArg_x21(v_e_494_, v___x_558_);
v___x_560_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___x_559_, v___y_498_);
lean_dec_ref(v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = lean_nat_add(v_a_561_, v___x_557_);
lean_dec(v_a_561_);
v___x_563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v___x_554_, v___x_554_, v_e_494_, v_numArgs_552_, v___x_562_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec_ref(v_e_494_);
lean_dec(v___x_554_);
return v___x_563_;
}
else
{
lean_dec(v___x_554_);
lean_dec(v_numArgs_552_);
lean_dec_ref(v_e_494_);
return v___x_560_;
}
}
}
else
{
lean_dec(v_a_550_);
goto v___jp_500_;
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_e_494_);
v_a_564_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_549_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_549_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_dec_ref(v___x_547_);
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
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_530_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_530_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_530_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_530_;
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
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_le(v___x_511_, v___x_511_);
if (v___x_516_ == 0)
{
if (v___x_512_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_518_ = v___x_508_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_510_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
size_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_usize_of_nat(v___x_511_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_506_, v___x_504_, v___x_520_, v___x_510_);
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_521_);
v___x_523_ = v___x_508_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
size_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = lean_usize_of_nat(v___x_511_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_506_, v___x_504_, v___x_525_, v___x_510_);
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_526_);
v___x_528_ = v___x_508_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_505_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_505_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_a_539_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_501_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_501_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0___boxed(lean_object* v_x_572_, lean_object* v_e_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_NormCast_countCoes___lam__0(v_x_572_, v_e_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_x_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___f_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Meta_NormCast_countCoes___lam__0___boxed), 7, 0);
v___x_587_ = 0;
v___x_588_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_580_, v___f_586_, v___x_587_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___boxed(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_NormCast_countCoes(v_e_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg___boxed(lean_object* v_upperBound_596_, lean_object* v___x_597_, lean_object* v_e_598_, lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_596_, v___x_597_, v_e_598_, v_a_599_, v_b_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v_e_598_);
lean_dec(v___x_597_);
lean_dec(v_upperBound_596_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0___boxed(lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_bs_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v_sz_boxed_615_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_616_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_boxed_615_, v_i_boxed_616_, v_bs_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(lean_object* v_upperBound_618_, lean_object* v___x_619_, lean_object* v_e_620_, lean_object* v_inst_621_, lean_object* v_R_622_, lean_object* v_a_623_, lean_object* v_b_624_, lean_object* v_c_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_618_, v___x_619_, v_e_620_, v_a_623_, v_b_624_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___boxed(lean_object* v_upperBound_632_, lean_object* v___x_633_, lean_object* v_e_634_, lean_object* v_inst_635_, lean_object* v_R_636_, lean_object* v_a_637_, lean_object* v_b_638_, lean_object* v_c_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(v_upperBound_632_, v___x_633_, v_e_634_, v_inst_635_, v_R_636_, v_a_637_, v_b_638_, v_c_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v_e_634_);
lean_dec(v___x_633_);
lean_dec(v_upperBound_632_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes(lean_object* v_e_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; 
lean_inc_ref(v_e_646_);
v___x_652_ = l_Lean_Meta_NormCast_countCoes(v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_646_, v_a_650_);
lean_dec_ref(v_e_646_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_nat_sub(v_a_653_, v_a_655_);
lean_dec(v_a_655_);
lean_dec(v_a_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_dec(v_a_653_);
return v___x_654_;
}
}
else
{
lean_dec_ref(v_e_646_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes___boxed(lean_object* v_e_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_NormCast_countInternalCoes(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(lean_object* v_type_671_, lean_object* v_k_672_, uint8_t v_cleanupAnnotations_673_, uint8_t v_whnfType_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___f_680_; lean_object* v___x_681_; 
v___f_680_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_680_, 0, v_k_672_);
v___x_681_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_671_, v___f_680_, v_cleanupAnnotations_673_, v_whnfType_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg___boxed(lean_object* v_type_698_, lean_object* v_k_699_, lean_object* v_cleanupAnnotations_700_, lean_object* v_whnfType_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_707_; uint8_t v_whnfType_boxed_708_; lean_object* v_res_709_; 
v_cleanupAnnotations_boxed_707_ = lean_unbox(v_cleanupAnnotations_700_);
v_whnfType_boxed_708_ = lean_unbox(v_whnfType_701_);
v_res_709_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_698_, v_k_699_, v_cleanupAnnotations_boxed_707_, v_whnfType_boxed_708_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(lean_object* v_00_u03b1_710_, lean_object* v_type_711_, lean_object* v_k_712_, uint8_t v_cleanupAnnotations_713_, uint8_t v_whnfType_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_711_, v_k_712_, v_cleanupAnnotations_713_, v_whnfType_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___boxed(lean_object* v_00_u03b1_721_, lean_object* v_type_722_, lean_object* v_k_723_, lean_object* v_cleanupAnnotations_724_, lean_object* v_whnfType_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_731_; uint8_t v_whnfType_boxed_732_; lean_object* v_res_733_; 
v_cleanupAnnotations_boxed_731_ = lean_unbox(v_cleanupAnnotations_724_);
v_whnfType_boxed_732_ = lean_unbox(v_whnfType_725_);
v_res_733_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(v_00_u03b1_721_, v_type_722_, v_k_723_, v_cleanupAnnotations_boxed_731_, v_whnfType_boxed_732_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(lean_object* v_msgData_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; lean_object* v_env_741_; uint8_t v___x_742_; lean_object* v_env_743_; lean_object* v___x_744_; lean_object* v_toCold_745_; lean_object* v_mctx_746_; lean_object* v_lctx_747_; lean_object* v_options_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_740_ = lean_st_ref_get(v___y_738_);
v_env_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_env_741_);
lean_dec(v___x_740_);
v___x_742_ = 0;
v_env_743_ = l_Lean_Environment_setRecordingDeps(v_env_741_, v___x_742_);
v___x_744_ = lean_st_ref_get(v___y_736_);
v_toCold_745_ = lean_ctor_get(v___y_737_, 0);
v_mctx_746_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_mctx_746_);
lean_dec(v___x_744_);
v_lctx_747_ = lean_ctor_get(v___y_735_, 2);
v_options_748_ = lean_ctor_get(v_toCold_745_, 2);
lean_inc_ref(v_options_748_);
lean_inc_ref(v_lctx_747_);
v___x_749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_749_, 0, v_env_743_);
lean_ctor_set(v___x_749_, 1, v_mctx_746_);
lean_ctor_set(v___x_749_, 2, v_lctx_747_);
lean_ctor_set(v___x_749_, 3, v_options_748_);
v___x_750_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_msgData_734_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0___boxed(lean_object* v_msgData_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msgData_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_ref_765_; lean_object* v___x_766_; lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
v_ref_765_ = lean_ctor_get(v___y_762_, 2);
v___x_766_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_775_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_inc(v_ref_765_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_ref_765_);
lean_ctor_set(v___x_771_, 1, v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 1);
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg___boxed(lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__0));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__2));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__4));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__5, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5);
v___x_793_ = l_Lean_MessageData_note(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__7));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__13));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0(lean_object* v_x_806_, lean_object* v_ty_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___x_823_; 
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
v___x_823_ = lean_whnf(v_ty_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_934_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__10));
v___x_935_ = lean_unsigned_to_nat(3u);
v___x_936_ = l_Lean_Expr_isAppOfArity(v_a_824_, v___x_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_937_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__12));
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = l_Lean_Expr_isAppOfArity(v_a_824_, v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v___x_940_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__14, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14);
v___x_941_ = l_Lean_indentExpr(v_a_824_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_942_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_952_ = l_Lean_Expr_getAppNumArgs(v_a_824_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_sub(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
lean_inc(v___x_954_);
v___x_955_ = l_Lean_Expr_getRevArg_x21(v_a_824_, v___x_954_);
v___x_956_ = lean_nat_sub(v___x_954_, v___x_953_);
lean_dec(v___x_954_);
v___x_957_ = l_Lean_Expr_getRevArg_x21(v_a_824_, v___x_956_);
v_fst_902_ = v___x_955_;
v_snd_903_ = v___x_957_;
v___y_904_ = v___y_808_;
v___y_905_ = v___y_809_;
v___y_906_ = v___y_810_;
v___y_907_ = v___y_811_;
goto v___jp_901_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = l_Lean_Expr_getAppNumArgs(v_a_824_);
v___x_960_ = lean_nat_sub(v___x_959_, v___x_958_);
v___x_961_ = lean_nat_sub(v___x_960_, v___x_958_);
lean_dec(v___x_960_);
v___x_962_ = l_Lean_Expr_getRevArg_x21(v_a_824_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(2u);
v___x_964_ = lean_nat_sub(v___x_959_, v___x_963_);
lean_dec(v___x_959_);
v___x_965_ = lean_nat_sub(v___x_964_, v___x_958_);
lean_dec(v___x_964_);
v___x_966_ = l_Lean_Expr_getRevArg_x21(v_a_824_, v___x_965_);
v_fst_902_ = v___x_962_;
v_snd_903_ = v___x_966_;
v___y_904_ = v___y_808_;
v___y_905_ = v___y_809_;
v___y_906_ = v___y_810_;
v___y_907_ = v___y_811_;
goto v___jp_901_;
}
v___jp_825_:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_826_, v___y_832_);
lean_dec_ref(v___y_826_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_828_, v___y_832_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
lean_inc_ref(v___y_828_);
v___x_837_ = l_Lean_Meta_NormCast_countInternalCoes(v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_876_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_876_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_876_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_876_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_nat_dec_eq(v_a_834_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_dec_eq(v_a_834_, v___x_844_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
lean_dec(v_a_838_);
lean_dec_ref(v___y_828_);
v___x_846_ = lean_nat_dec_lt(v_a_836_, v_a_834_);
lean_dec(v_a_834_);
lean_dec(v_a_836_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_840_);
v___x_847_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__1, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1);
v___x_848_ = l_Lean_indentExpr(v_a_824_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
lean_inc_ref(v___y_827_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___y_827_);
v___x_851_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_850_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v_a_824_);
v___x_852_ = 2;
v___x_853_ = lean_box(v___x_852_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_853_);
v___x_855_ = v___x_840_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
uint8_t v___x_857_; 
lean_del_object(v___x_840_);
lean_dec(v_a_834_);
lean_dec(v_a_824_);
v___x_857_ = lean_nat_dec_eq(v_a_836_, v___x_842_);
lean_dec(v_a_836_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_a_838_);
v___x_858_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__3, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3);
v___x_859_ = l_Lean_indentExpr(v___y_828_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
lean_inc_ref(v___y_827_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___y_827_);
v___x_862_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_861_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_dec_ref(v___y_828_);
v___y_814_ = v___x_842_;
v___y_815_ = v_a_838_;
goto v___jp_813_;
}
}
}
else
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec(v_a_838_);
lean_dec(v_a_836_);
lean_dec(v_a_834_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_824_);
v___x_871_ = 0;
v___x_872_ = lean_box(v___x_871_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_872_);
v___x_874_ = v___x_840_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_a_836_);
lean_dec(v_a_834_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_824_);
v_a_877_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_837_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_837_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_834_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_824_);
v_a_885_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_835_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_835_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___y_828_);
lean_dec(v_a_824_);
v_a_893_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_833_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_833_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
v___jp_901_:
{
lean_object* v___x_908_; 
lean_inc_ref(v_fst_902_);
v___x_908_ = l_Lean_Meta_NormCast_countCoes(v_fst_902_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__6, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_nat_dec_eq(v_a_909_, v___x_911_);
lean_dec(v_a_909_);
if (v___x_912_ == 0)
{
v___y_826_ = v_fst_902_;
v___y_827_ = v___x_910_;
v___y_828_ = v_snd_903_;
v___y_829_ = v___y_904_;
v___y_830_ = v___y_905_;
v___y_831_ = v___y_906_;
v___y_832_ = v___y_907_;
goto v___jp_825_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v_snd_903_);
lean_dec(v_a_824_);
v___x_913_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__8, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8);
v___x_914_ = l_Lean_indentExpr(v_fst_902_);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_910_);
v___x_917_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_916_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_snd_903_);
lean_dec_ref(v_fst_902_);
lean_dec(v_a_824_);
v_a_926_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_908_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_908_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_823_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_823_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
v___jp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = lean_nat_dec_eq(v___y_815_, v___y_814_);
lean_dec(v___y_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = 1;
v___x_818_ = lean_box(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = 2;
v___x_821_ = lean_box(v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___boxed(lean_object* v_x_975_, lean_object* v_ty_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_NormCast_classifyType___lam__0(v_x_975_, v_ty_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_x_975_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType(lean_object* v_ty_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___f_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
v___f_990_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___closed__0));
v___x_991_ = 0;
v___x_992_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_ty_984_, v___f_990_, v___x_991_, v___x_991_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___boxed(lean_object* v_ty_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_NormCast_classifyType(v_ty_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(lean_object* v_00_u03b1_1000_, lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(v_00_u03b1_1008_, v_msg_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1033_ = l_Lean_Meta_registerSimpAttr(v___x_1030_, v___x_1031_, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2____boxed(lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
return v_res_1035_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = l_Lean_Meta_instInhabitedSimpEntry_default;
v___x_1037_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0);
v___x_1039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default;
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1053_ = l_Lean_Name_append(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1059_ = l_Lean_Name_append(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1065_ = l_Lean_Name_append(v___x_1064_, v___x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1068_ = l_Lean_Meta_mkSimpExt(v___x_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1071_ = l_Lean_Meta_mkSimpExt(v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1074_ = l_Lean_Meta_mkSimpExt(v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1069_);
lean_ctor_set(v___x_1079_, 1, v_a_1072_);
lean_ctor_set(v___x_1079_, 2, v_a_1075_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
v_a_1084_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1074_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1069_);
v_a_1092_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1071_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1071_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1068_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1068_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2____boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim(lean_object* v_decl_1110_, uint8_t v_kind_1111_, lean_object* v_prio_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_up_1119_; uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1118_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1119_ = lean_ctor_get(v___x_1118_, 0);
v___x_1120_ = 1;
v___x_1121_ = 0;
lean_inc_ref(v_up_1119_);
v___x_1122_ = l_Lean_Meta_addSimpTheorem(v_up_1119_, v_decl_1110_, v___x_1120_, v___x_1121_, v_kind_1111_, v_prio_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim___boxed(lean_object* v_decl_1123_, lean_object* v_kind_1124_, lean_object* v_prio_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
uint8_t v_kind_boxed_1131_; lean_object* v_res_1132_; 
v_kind_boxed_1131_ = lean_unbox(v_kind_1124_);
v_res_1132_ = l_Lean_Meta_NormCast_addElim(v_decl_1123_, v_kind_boxed_1131_, v_prio_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove(lean_object* v_decl_1133_, uint8_t v_kind_1134_, lean_object* v_prio_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1142_ = 1;
v___x_1143_ = 0;
lean_inc(v_prio_1135_);
lean_inc(v_decl_1133_);
v___x_1144_ = l_Lean_Meta_addSimpTheorem(v___x_1141_, v_decl_1133_, v___x_1142_, v___x_1143_, v_kind_1134_, v_prio_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v_up_1146_; lean_object* v_down_1147_; lean_object* v___x_1148_; 
lean_dec_ref_known(v___x_1144_, 1);
v___x_1145_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1146_ = lean_ctor_get(v___x_1145_, 0);
v_down_1147_ = lean_ctor_get(v___x_1145_, 1);
lean_inc(v_prio_1135_);
lean_inc(v_decl_1133_);
lean_inc_ref(v_up_1146_);
v___x_1148_ = l_Lean_Meta_addSimpTheorem(v_up_1146_, v_decl_1133_, v___x_1142_, v___x_1142_, v_kind_1134_, v_prio_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1148_, 1);
lean_inc_ref(v_down_1147_);
v___x_1149_ = l_Lean_Meta_addSimpTheorem(v_down_1147_, v_decl_1133_, v___x_1142_, v___x_1143_, v_kind_1134_, v_prio_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1149_;
}
else
{
lean_dec(v_prio_1135_);
lean_dec(v_decl_1133_);
return v___x_1148_;
}
}
else
{
lean_dec(v_prio_1135_);
lean_dec(v_decl_1133_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove___boxed(lean_object* v_decl_1150_, lean_object* v_kind_1151_, lean_object* v_prio_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
uint8_t v_kind_boxed_1158_; lean_object* v_res_1159_; 
v_kind_boxed_1158_ = lean_unbox(v_kind_1151_);
v_res_1159_ = l_Lean_Meta_NormCast_addMove(v_decl_1150_, v_kind_boxed_1158_, v_prio_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash(lean_object* v_decl_1160_, uint8_t v_kind_1161_, lean_object* v_prio_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1169_ = 1;
v___x_1170_ = 0;
lean_inc(v_prio_1162_);
lean_inc(v_decl_1160_);
v___x_1171_ = l_Lean_Meta_addSimpTheorem(v___x_1168_, v_decl_1160_, v___x_1169_, v___x_1170_, v_kind_1161_, v_prio_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1172_; lean_object* v_down_1173_; lean_object* v_squash_1174_; lean_object* v___x_1175_; 
lean_dec_ref_known(v___x_1171_, 1);
v___x_1172_ = l_Lean_Meta_NormCast_normCastExt;
v_down_1173_ = lean_ctor_get(v___x_1172_, 1);
v_squash_1174_ = lean_ctor_get(v___x_1172_, 2);
lean_inc(v_prio_1162_);
lean_inc(v_decl_1160_);
lean_inc_ref(v_squash_1174_);
v___x_1175_ = l_Lean_Meta_addSimpTheorem(v_squash_1174_, v_decl_1160_, v___x_1169_, v___x_1170_, v_kind_1161_, v_prio_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref_known(v___x_1175_, 1);
lean_inc_ref(v_down_1173_);
v___x_1176_ = l_Lean_Meta_addSimpTheorem(v_down_1173_, v_decl_1160_, v___x_1169_, v___x_1170_, v_kind_1161_, v_prio_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
return v___x_1176_;
}
else
{
lean_dec(v_prio_1162_);
lean_dec(v_decl_1160_);
return v___x_1175_;
}
}
else
{
lean_dec(v_prio_1162_);
lean_dec(v_decl_1160_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash___boxed(lean_object* v_decl_1177_, lean_object* v_kind_1178_, lean_object* v_prio_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
uint8_t v_kind_boxed_1185_; lean_object* v_res_1186_; 
v_kind_boxed_1185_ = lean_unbox(v_kind_1178_);
v_res_1186_ = l_Lean_Meta_NormCast_addSquash(v_decl_1177_, v_kind_boxed_1185_, v_prio_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
lean_ctor_set(v___x_1193_, 2, v___x_1192_);
lean_ctor_set(v___x_1193_, 3, v___x_1192_);
lean_ctor_set(v___x_1193_, 4, v___x_1191_);
lean_ctor_set(v___x_1193_, 5, v___x_1191_);
lean_ctor_set(v___x_1193_, 6, v___x_1191_);
lean_ctor_set(v___x_1193_, 7, v___x_1191_);
lean_ctor_set(v___x_1193_, 8, v___x_1191_);
lean_ctor_set(v___x_1193_, 9, v___x_1191_);
lean_ctor_set(v___x_1193_, 10, v___x_1191_);
lean_ctor_set(v___x_1193_, 11, v___x_1190_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_unsigned_to_nat(32u);
v___x_1195_ = lean_mk_empty_array_with_capacity(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = ((size_t)5ULL);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_unsigned_to_nat(32u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1202_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
lean_ctor_set(v___x_1202_, 2, v___x_1198_);
lean_ctor_set(v___x_1202_, 3, v___x_1198_);
lean_ctor_set_usize(v___x_1202_, 4, v___x_1197_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = lean_box(1);
v___x_1204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1204_);
lean_ctor_set(v___x_1206_, 2, v___x_1203_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_1239_ = l_Lean_stringToMessageData(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1240_, lean_object* v_declHint_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_env_1246_; uint8_t v___x_1247_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_st_ref_get(v___y_1242_);
v_env_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_env_1246_);
lean_dec(v___x_1245_);
v___x_1247_ = l_Lean_Name_isAnonymous(v_declHint_1241_);
if (v___x_1247_ == 0)
{
uint8_t v_isExporting_1248_; 
v_isExporting_1248_ = lean_ctor_get_uint8(v_env_1246_, sizeof(void*)*13);
if (v_isExporting_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v_env_1246_);
lean_dec(v_declHint_1241_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_msg_1240_);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_inc_ref(v_env_1246_);
v___x_1250_ = l_Lean_Environment_setExporting(v_env_1246_, v___x_1247_);
lean_inc(v_declHint_1241_);
lean_inc_ref(v___x_1250_);
v___x_1251_ = l_Lean_Environment_contains(v___x_1250_, v_declHint_1241_, v_isExporting_1248_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_env_1246_);
lean_dec(v_declHint_1241_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_msg_1240_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_c_1258_; lean_object* v___x_1259_; 
v___x_1253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1255_ = l_Lean_Options_empty;
v___x_1256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1250_);
lean_ctor_set(v___x_1256_, 1, v___x_1253_);
lean_ctor_set(v___x_1256_, 2, v___x_1254_);
lean_ctor_set(v___x_1256_, 3, v___x_1255_);
lean_inc(v_declHint_1241_);
v___x_1257_ = l_Lean_MessageData_ofConstName(v_declHint_1241_, v___x_1247_);
v_c_1258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1258_, 0, v___x_1256_);
lean_ctor_set(v_c_1258_, 1, v___x_1257_);
v___x_1259_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1246_, v_declHint_1241_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v_env_1246_);
lean_dec(v_declHint_1241_);
v___x_1260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_c_1258_);
v___x_1262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = l_Lean_MessageData_note(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_msg_1240_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
else
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1323_; 
v_val_1267_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1269_ = v___x_1259_;
v_isShared_1270_ = v_isSharedCheck_1323_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v___x_1259_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1323_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v_modules_1272_; lean_object* v_moduleNames_1273_; lean_object* v_mod_1274_; uint8_t v___y_1276_; uint8_t v___x_1306_; 
v___x_1271_ = l_Lean_Environment_header(v_env_1246_);
lean_dec_ref(v_env_1246_);
v_modules_1272_ = lean_ctor_get(v___x_1271_, 3);
lean_inc_ref(v_modules_1272_);
v_moduleNames_1273_ = lean_ctor_get(v___x_1271_, 4);
lean_inc_ref(v_moduleNames_1273_);
lean_dec_ref(v___x_1271_);
v_mod_1274_ = lean_array_get(v___x_1244_, v_moduleNames_1273_, v_val_1267_);
lean_dec_ref(v_moduleNames_1273_);
v___x_1306_ = l_Lean_isPrivateName(v_declHint_1241_);
lean_dec(v_declHint_1241_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_array_get_size(v_modules_1272_);
v___x_1308_ = lean_nat_dec_lt(v_val_1267_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_modules_1272_);
lean_dec(v_val_1267_);
v___y_1276_ = v___x_1306_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1309_; lean_object* v_toImport_1310_; uint8_t v_isExported_1311_; 
v___x_1309_ = lean_array_fget(v_modules_1272_, v_val_1267_);
lean_dec(v_val_1267_);
lean_dec_ref(v_modules_1272_);
v_toImport_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc_ref(v_toImport_1310_);
lean_dec(v___x_1309_);
v_isExported_1311_ = lean_ctor_get_uint8(v_toImport_1310_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1310_);
v___y_1276_ = v_isExported_1311_;
goto v___jp_1275_;
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v_modules_1272_);
lean_del_object(v___x_1269_);
lean_dec(v_val_1267_);
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_c_1258_);
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_MessageData_ofName(v_mod_1274_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = l_Lean_MessageData_note(v___x_1319_);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_msg_1240_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
v___jp_1275_:
{
if (v___y_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_c_1258_);
v___x_1279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_MessageData_ofName(v_mod_1274_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_MessageData_note(v___x_1284_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_msg_1240_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1286_);
v___x_1288_ = v___x_1269_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_c_1258_);
v___x_1292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = l_Lean_MessageData_ofName(v_mod_1274_);
lean_inc_ref(v___x_1294_);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_1297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1294_);
v___x_1299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = l_Lean_MessageData_note(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_msg_1240_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1302_);
v___x_1304_ = v___x_1269_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
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
lean_object* v___x_1324_; 
lean_dec_ref(v_env_1246_);
lean_dec(v_declHint_1241_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_msg_1240_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1325_, lean_object* v_declHint_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1325_, v_declHint_1326_, v___y_1327_);
lean_dec(v___y_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1330_, lean_object* v_declHint_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
v___x_1337_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1330_, v_declHint_1331_, v___y_1335_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = l_Lean_unknownIdentifierMessageTag;
v___x_1343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_a_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1343_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1348_, lean_object* v_declHint_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1348_, v_declHint_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1356_, lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_toCold_1363_; lean_object* v_currRecDepth_1364_; lean_object* v_ref_1365_; uint16_t v_optionFlags_1366_; uint8_t v_suppressElabErrors_1367_; uint8_t v_isRecordingDeps_1368_; lean_object* v_ref_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_toCold_1363_ = lean_ctor_get(v___y_1360_, 0);
v_currRecDepth_1364_ = lean_ctor_get(v___y_1360_, 1);
v_ref_1365_ = lean_ctor_get(v___y_1360_, 2);
v_optionFlags_1366_ = lean_ctor_get_uint16(v___y_1360_, sizeof(void*)*3);
v_suppressElabErrors_1367_ = lean_ctor_get_uint8(v___y_1360_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1368_ = lean_ctor_get_uint8(v___y_1360_, sizeof(void*)*3 + 3);
v_ref_1369_ = l_Lean_replaceRef(v_ref_1356_, v_ref_1365_);
lean_inc(v_currRecDepth_1364_);
lean_inc_ref(v_toCold_1363_);
v___x_1370_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1370_, 0, v_toCold_1363_);
lean_ctor_set(v___x_1370_, 1, v_currRecDepth_1364_);
lean_ctor_set(v___x_1370_, 2, v_ref_1369_);
lean_ctor_set_uint16(v___x_1370_, sizeof(void*)*3, v_optionFlags_1366_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 2, v_suppressElabErrors_1367_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*3 + 3, v_isRecordingDeps_1368_);
v___x_1371_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_1357_, v___y_1358_, v___y_1359_, v___x_1370_, v___y_1361_);
lean_dec_ref_known(v___x_1370_, 3);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1372_, lean_object* v_msg_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1372_, v_msg_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v_ref_1372_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1380_, lean_object* v_msg_1381_, lean_object* v_declHint_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1381_, v_declHint_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1380_, v_a_1389_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1391_, lean_object* v_msg_1392_, lean_object* v_declHint_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1391_, v_msg_1392_, v_declHint_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_ref_1391_);
return v_res_1399_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1406_, lean_object* v_constName_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1413_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1414_ = 0;
lean_inc(v_constName_1407_);
v___x_1415_ = l_Lean_MessageData_ofConstName(v_constName_1407_, v___x_1414_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1413_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1406_, v___x_1418_, v_constName_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1420_, lean_object* v_constName_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1420_, v_constName_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v_ref_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_ref_1434_; lean_object* v___x_1435_; 
v_ref_1434_ = lean_ctor_get(v___y_1431_, 2);
v___x_1435_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1434_, v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(lean_object* v_constName_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_env_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1449_ = lean_st_ref_get(v___y_1447_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_ref(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1451_ = 0;
lean_inc(v_constName_1443_);
v___x_1452_ = l_Lean_Environment_findConstVal_x3f(v_env_1450_, v_constName_1443_, v___x_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1453_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_constName_1443_);
v_val_1454_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_val_1454_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 0);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_val_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0___boxed(lean_object* v_constName_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_constName_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer(lean_object* v_decl_1469_, uint8_t v_kind_1470_, lean_object* v_prio_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; 
lean_inc(v_decl_1469_);
v___x_1477_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_decl_1469_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v_type_1479_; lean_object* v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v_type_1479_ = lean_ctor_get(v_a_1478_, 2);
lean_inc_ref(v_type_1479_);
lean_dec(v_a_1478_);
v___x_1480_ = l_Lean_Meta_NormCast_classifyType(v_type_1479_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; uint8_t v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = lean_unbox(v_a_1481_);
lean_dec(v_a_1481_);
switch(v___x_1482_)
{
case 0:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Meta_NormCast_addElim(v_decl_1469_, v_kind_1470_, v_prio_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1483_;
}
case 1:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Meta_NormCast_addMove(v_decl_1469_, v_kind_1470_, v_prio_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1484_;
}
default: 
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Meta_NormCast_addSquash(v_decl_1469_, v_kind_1470_, v_prio_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_prio_1471_);
lean_dec(v_decl_1469_);
v_a_1486_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1480_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1480_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_prio_1471_);
lean_dec(v_decl_1469_);
v_a_1494_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1477_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1477_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer___boxed(lean_object* v_decl_1502_, lean_object* v_kind_1503_, lean_object* v_prio_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
uint8_t v_kind_boxed_1510_; lean_object* v_res_1511_; 
v_kind_boxed_1510_ = lean_unbox(v_kind_1503_);
v_res_1511_ = l_Lean_Meta_NormCast_addInfer(v_decl_1502_, v_kind_boxed_1510_, v_prio_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(lean_object* v_00_u03b1_1512_, lean_object* v_constName_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_constName_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(v_00_u03b1_1520_, v_constName_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1528_, lean_object* v_ref_1529_, lean_object* v_constName_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1529_, v_constName_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_ref_1538_, lean_object* v_constName_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(v_00_u03b1_1537_, v_ref_1538_, v_constName_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v_ref_1538_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1546_, lean_object* v_ref_1547_, lean_object* v_msg_1548_, lean_object* v_declHint_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1547_, v_msg_1548_, v_declHint_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1556_, lean_object* v_ref_1557_, lean_object* v_msg_1558_, lean_object* v_declHint_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1556_, v_ref_1557_, v_msg_1558_, v_declHint_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1557_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1566_, lean_object* v_declHint_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1566_, v_declHint_1567_, v___y_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1574_, lean_object* v_declHint_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1574_, v_declHint_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1582_, lean_object* v_ref_1583_, lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1583_, v_msg_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_ref_1592_, lean_object* v_msg_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1591_, v_ref_1592_, v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v_ref_1592_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(lean_object* v_msg_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___f_1607_; lean_object* v___x_962__overap_1608_; lean_object* v___x_1609_; 
v___f_1607_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0));
v___x_962__overap_1608_ = lean_panic_fn_borrowed(v___f_1607_, v_msg_1601_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
v___x_1609_ = lean_apply_5(v___x_962__overap_1608_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___boxed(lean_object* v_msg_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v_msg_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1623_ = lean_unsigned_to_nat(11u);
v___x_1624_ = lean_unsigned_to_nat(165u);
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1627_ = l_mkPanicMessageWithDecl(v___x_1626_, v___x_1625_, v___x_1624_, v___x_1623_, v___x_1622_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1629_ = lean_unsigned_to_nat(71u);
v___x_1630_ = lean_unsigned_to_nat(158u);
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1633_ = l_mkPanicMessageWithDecl(v___x_1632_, v___x_1631_, v___x_1630_, v___x_1629_, v___x_1628_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v_decl_1634_, uint8_t v_kind_1635_, lean_object* v_stx_1636_, lean_object* v___x_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_x_1640_, lean_object* v_label_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = l_Lean_Syntax_getArg(v_stx_1636_, v___x_1637_);
v___x_1676_ = l_Lean_Syntax_isNone(v___x_1675_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; 
lean_inc(v___x_1675_);
v___x_1677_ = l_Lean_Syntax_matchesNull(v___x_1675_, v___x_1638_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1675_);
lean_dec(v_decl_1634_);
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1679_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1678_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1679_;
}
else
{
lean_object* v_prio_1680_; lean_object* v___x_1681_; 
v_prio_1680_ = l_Lean_Syntax_getArg(v___x_1675_, v___x_1639_);
lean_dec(v___x_1675_);
v___x_1681_ = l_Lean_Syntax_isNatLit_x3f(v_prio_1680_);
lean_dec(v_prio_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
v___y_1670_ = v___y_1643_;
v___y_1671_ = v___y_1644_;
v___y_1672_ = v___y_1645_;
v___y_1673_ = v___y_1642_;
goto v___jp_1669_;
}
else
{
lean_object* v_val_1682_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___y_1648_ = v___y_1645_;
v___y_1649_ = v___y_1644_;
v___y_1650_ = v___y_1643_;
v___y_1651_ = v___y_1642_;
v___y_1652_ = v_val_1682_;
goto v___jp_1647_;
}
}
}
else
{
lean_dec(v___x_1675_);
v___y_1670_ = v___y_1643_;
v___y_1671_ = v___y_1644_;
v___y_1672_ = v___y_1645_;
v___y_1673_ = v___y_1642_;
goto v___jp_1669_;
}
v___jp_1647_:
{
if (lean_obj_tag(v_label_1641_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Meta_NormCast_addInfer(v_decl_1634_, v_kind_1635_, v___y_1652_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1655_; 
v_val_1654_ = lean_ctor_get(v_label_1641_, 0);
v___x_1655_ = l_Lean_Syntax_isStrLit_x3f(v_val_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_NormCast_addInfer(v_decl_1634_, v_kind_1635_, v___y_1652_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1656_;
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_val_1657_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1659_ = lean_string_dec_eq(v_val_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1661_ = lean_string_dec_eq(v_val_1657_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1663_ = lean_string_dec_eq(v_val_1657_, v___x_1662_);
lean_dec(v_val_1657_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___y_1652_);
lean_dec(v_decl_1634_);
v___x_1664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1665_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1664_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_NormCast_addSquash(v_decl_1634_, v_kind_1635_, v___y_1652_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1666_;
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_val_1657_);
v___x_1667_ = l_Lean_Meta_NormCast_addMove(v_decl_1634_, v_kind_1635_, v___y_1652_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1667_;
}
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_val_1657_);
v___x_1668_ = l_Lean_Meta_NormCast_addElim(v_decl_1634_, v_kind_1635_, v___y_1652_, v___y_1651_, v___y_1650_, v___y_1649_, v___y_1648_);
return v___x_1668_;
}
}
}
}
v___jp_1669_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_unsigned_to_nat(1000u);
v___y_1648_ = v___y_1672_;
v___y_1649_ = v___y_1671_;
v___y_1650_ = v___y_1670_;
v___y_1651_ = v___y_1673_;
v___y_1652_ = v___x_1674_;
goto v___jp_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_decl_1683_, lean_object* v_kind_1684_, lean_object* v_stx_1685_, lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v_x_1689_, lean_object* v_label_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v_kind_boxed_1696_; lean_object* v_res_1697_; 
v_kind_boxed_1696_ = lean_unbox(v_kind_1684_);
v_res_1697_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1683_, v_kind_boxed_1696_, v_stx_1685_, v___x_1686_, v___x_1687_, v___x_1688_, v_x_1689_, v_label_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v_label_1690_);
lean_dec(v___x_1688_);
lean_dec(v___x_1687_);
lean_dec(v___x_1686_);
lean_dec(v_stx_1685_);
return v_res_1697_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1706_; uint64_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1710_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set_uint64(v___x_1710_, sizeof(void*)*1, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1714_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
lean_ctor_set(v___x_1714_, 2, v___x_1713_);
lean_ctor_set(v___x_1714_, 3, v___x_1713_);
lean_ctor_set(v___x_1714_, 4, v___x_1713_);
lean_ctor_set(v___x_1714_, 5, v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
lean_ctor_set(v___x_1716_, 2, v___x_1715_);
lean_ctor_set(v___x_1716_, 3, v___x_1715_);
lean_ctor_set(v___x_1716_, 4, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_decl_1723_, lean_object* v_stx_1724_, uint8_t v_kind_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___y_1754_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
lean_inc_ref(v___x_1718_);
v___x_1731_ = l_Lean_Name_mkStr4(v___x_1718_, v___x_1729_, v___x_1730_, v___x_1719_);
lean_inc(v_stx_1724_);
v___x_1732_ = l_Lean_Syntax_isOfKind(v_stx_1724_, v___x_1731_);
lean_dec(v___x_1731_);
v___x_1733_ = 1;
v___x_1734_ = 0;
v___x_1735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1737_ = lean_unsigned_to_nat(32u);
v___x_1738_ = lean_mk_empty_array_with_capacity(v___x_1737_);
v___x_1739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1740_ = ((size_t)5ULL);
lean_inc_n(v___x_1720_, 7);
v___x_1741_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1738_);
lean_ctor_set(v___x_1741_, 2, v___x_1720_);
lean_ctor_set(v___x_1741_, 3, v___x_1720_);
lean_ctor_set_usize(v___x_1741_, 4, v___x_1740_);
v___x_1742_ = lean_box(1);
lean_inc_ref(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1736_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
lean_ctor_set(v___x_1743_, 2, v___x_1742_);
v___x_1744_ = lean_mk_empty_array_with_capacity(v___x_1720_);
v___x_1745_ = lean_box(0);
lean_inc(v___x_1721_);
v___x_1746_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1746_, 0, v___x_1735_);
lean_ctor_set(v___x_1746_, 1, v___x_1721_);
lean_ctor_set(v___x_1746_, 2, v___x_1743_);
lean_ctor_set(v___x_1746_, 3, v___x_1744_);
lean_ctor_set(v___x_1746_, 4, v___x_1745_);
lean_ctor_set(v___x_1746_, 5, v___x_1720_);
lean_ctor_set(v___x_1746_, 6, v___x_1745_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*7, v___x_1734_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*7 + 1, v___x_1734_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*7 + 2, v___x_1734_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*7 + 3, v___x_1733_);
v___x_1747_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1748_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1720_);
lean_ctor_set(v___x_1748_, 1, v___x_1720_);
lean_ctor_set(v___x_1748_, 2, v___x_1720_);
lean_ctor_set(v___x_1748_, 3, v___x_1720_);
lean_ctor_set(v___x_1748_, 4, v___x_1736_);
lean_ctor_set(v___x_1748_, 5, v___x_1736_);
lean_ctor_set(v___x_1748_, 6, v___x_1736_);
lean_ctor_set(v___x_1748_, 7, v___x_1736_);
lean_ctor_set(v___x_1748_, 8, v___x_1736_);
lean_ctor_set(v___x_1748_, 9, v___x_1736_);
lean_ctor_set(v___x_1748_, 10, v___x_1736_);
lean_ctor_set(v___x_1748_, 11, v___x_1747_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1748_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
lean_ctor_set(v___x_1751_, 2, v___x_1721_);
lean_ctor_set(v___x_1751_, 3, v___x_1741_);
lean_ctor_set(v___x_1751_, 4, v___x_1750_);
v___x_1752_ = lean_st_mk_ref(v___x_1751_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_stx_1724_);
lean_dec(v_decl_1723_);
lean_dec(v___x_1720_);
lean_dec_ref(v___x_1718_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1765_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1764_, v___x_1746_, v___x_1752_, v___y_1726_, v___y_1727_);
lean_dec_ref_known(v___x_1746_, 7);
v___y_1754_ = v___x_1765_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = l_Lean_Syntax_getArg(v_stx_1724_, v___x_1766_);
v___x_1768_ = l_Lean_Syntax_isNone(v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
lean_inc(v___x_1767_);
v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1766_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v___x_1767_);
lean_dec(v_stx_1724_);
lean_dec(v_decl_1723_);
lean_dec(v___x_1720_);
lean_dec_ref(v___x_1718_);
v___x_1770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1771_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1770_, v___x_1746_, v___x_1752_, v___y_1726_, v___y_1727_);
lean_dec_ref_known(v___x_1746_, 7);
v___y_1754_ = v___x_1771_;
goto v___jp_1753_;
}
else
{
lean_object* v_label_1772_; 
v_label_1772_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1720_);
lean_dec(v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1778_ = l_Lean_Name_mkStr4(v___x_1718_, v___x_1729_, v___x_1730_, v___x_1777_);
lean_inc(v_label_1772_);
v___x_1779_ = l_Lean_Syntax_isOfKind(v_label_1772_, v___x_1778_);
lean_dec(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v_label_1772_);
lean_dec(v_stx_1724_);
lean_dec(v_decl_1723_);
lean_dec(v___x_1720_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1781_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1780_, v___x_1746_, v___x_1752_, v___y_1726_, v___y_1727_);
lean_dec_ref_known(v___x_1746_, 7);
v___y_1754_ = v___x_1781_;
goto v___jp_1753_;
}
else
{
goto v___jp_1773_;
}
}
else
{
lean_dec_ref(v___x_1718_);
goto v___jp_1773_;
}
v___jp_1773_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_label_1772_);
v___x_1776_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1723_, v_kind_1725_, v_stx_1724_, v___x_1722_, v___x_1766_, v___x_1720_, v___x_1774_, v___x_1775_, v___x_1746_, v___x_1752_, v___y_1726_, v___y_1727_);
lean_dec_ref_known(v___x_1746_, 7);
lean_dec_ref_known(v___x_1775_, 1);
lean_dec(v___x_1720_);
lean_dec(v_stx_1724_);
v___y_1754_ = v___x_1776_;
goto v___jp_1753_;
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1767_);
lean_dec_ref(v___x_1718_);
v___x_1782_ = lean_box(0);
v___x_1783_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1723_, v_kind_1725_, v_stx_1724_, v___x_1722_, v___x_1766_, v___x_1720_, v___x_1782_, v___x_1745_, v___x_1746_, v___x_1752_, v___y_1726_, v___y_1727_);
lean_dec_ref_known(v___x_1746_, 7);
lean_dec(v___x_1720_);
lean_dec(v_stx_1724_);
v___y_1754_ = v___x_1783_;
goto v___jp_1753_;
}
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
v_a_1755_ = lean_ctor_get(v___y_1754_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___y_1754_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1757_ = v___y_1754_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___y_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_st_ref_get(v___x_1752_);
lean_dec(v___x_1752_);
lean_dec(v___x_1759_);
if (v_isShared_1758_ == 0)
{
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1755_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_dec(v___x_1752_);
return v___y_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, lean_object* v___x_1788_, lean_object* v_decl_1789_, lean_object* v_stx_1790_, lean_object* v_kind_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_kind_boxed_1795_; lean_object* v_res_1796_; 
v_kind_boxed_1795_ = lean_unbox(v_kind_1791_);
v_res_1796_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1784_, v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_, v_decl_1789_, v_stx_1790_, v_kind_boxed_1795_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___x_1788_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v_toCold_1802_; lean_object* v_env_1803_; lean_object* v_options_1804_; uint8_t v___x_1805_; lean_object* v_env_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1801_ = lean_st_ref_get(v___y_1799_);
v_toCold_1802_ = lean_ctor_get(v___y_1798_, 0);
v_env_1803_ = lean_ctor_get(v___x_1801_, 0);
lean_inc_ref(v_env_1803_);
lean_dec(v___x_1801_);
v_options_1804_ = lean_ctor_get(v_toCold_1802_, 2);
v___x_1805_ = 0;
v_env_1806_ = l_Lean_Environment_setRecordingDeps(v_env_1803_, v___x_1805_);
v___x_1807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1808_ = lean_unsigned_to_nat(32u);
v___x_1809_ = lean_mk_empty_array_with_capacity(v___x_1808_);
lean_dec_ref(v___x_1809_);
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_1804_);
v___x_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1811_, 0, v_env_1806_);
lean_ctor_set(v___x_1811_, 1, v___x_1807_);
lean_ctor_set(v___x_1811_, 2, v___x_1810_);
lean_ctor_set(v___x_1811_, 3, v_options_1804_);
v___x_1812_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_msgData_1797_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msgData_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_ref_1823_; lean_object* v___x_1824_; lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
v_ref_1823_ = lean_ctor_get(v___y_1820_, 2);
v___x_1824_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msg_1819_, v___y_1820_, v___y_1821_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_inc(v_ref_1823_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_ref_1823_);
lean_ctor_set(v___x_1829_, 1, v_a_1825_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1845_, lean_object* v_decl_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1851_ = l_Lean_MessageData_ofName(v___x_1845_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v___x_1854_, v___y_1847_, v___y_1848_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1856_, lean_object* v_decl_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1856_, v_decl_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v_decl_1857_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1948_ = l_Lean_registerBuiltinAttribute(v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1951_, lean_object* v_msg_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1952_, v___y_1953_, v___y_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1957_, lean_object* v_msg_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(v_00_u03b1_1957_, v_msg_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1962_;
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
