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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpEntry_default;
lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___boxed(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normCastLabel"};
static const lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value;
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
static const lean_closure_object l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__26_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__25_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_NormCast_Label_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Meta_NormCast_Label_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg(lean_object* v_elim_23_){
_start:
{
lean_inc(v_elim_23_);
return v_elim_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___redArg___boxed(lean_object* v_elim_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_NormCast_Label_elim_elim___redArg(v_elim_24_);
lean_dec(v_elim_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_elim_29_){
_start:
{
lean_inc(v_elim_29_);
return v_elim_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_elim_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_elim_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Meta_NormCast_Label_elim_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_elim_33_);
lean_dec(v_elim_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg(lean_object* v_move_36_){
_start:
{
lean_inc(v_move_36_);
return v_move_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___redArg___boxed(lean_object* v_move_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_NormCast_Label_move_elim___redArg(v_move_37_);
lean_dec(v_move_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_move_42_){
_start:
{
lean_inc(v_move_42_);
return v_move_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_move_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_move_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Meta_NormCast_Label_move_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_move_46_);
lean_dec(v_move_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg(lean_object* v_squash_49_){
_start:
{
lean_inc(v_squash_49_);
return v_squash_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___redArg___boxed(lean_object* v_squash_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_NormCast_Label_squash_elim___redArg(v_squash_50_);
lean_dec(v_squash_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_squash_55_){
_start:
{
lean_inc(v_squash_55_);
return v_squash_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_squash_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_squash_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Meta_NormCast_Label_squash_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_squash_59_);
lean_dec(v_squash_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_Label_ofNat(lean_object* v_n_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_nat_dec_le(v_n_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_dec_le(v_n_62_, v___x_65_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 2;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_Label_ofNat___boxed(lean_object* v_n_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Meta_NormCast_Label_ofNat(v_n_70_);
lean_dec(v_n_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_NormCast_instDecidableEqLabel(uint8_t v_x_73_, uint8_t v_y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_x_73_);
v___x_76_ = l_Lean_Meta_NormCast_Label_ctorIdx(v_y_74_);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
lean_dec(v___x_76_);
lean_dec(v___x_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instDecidableEqLabel___boxed(lean_object* v_x_78_, lean_object* v_y_79_){
_start:
{
uint8_t v_x_20__boxed_80_; uint8_t v_y_21__boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_x_20__boxed_80_ = lean_unbox(v_x_78_);
v_y_21__boxed_81_ = lean_unbox(v_y_79_);
v_res_82_ = l_Lean_Meta_NormCast_instDecidableEqLabel(v_x_20__boxed_80_, v_y_21__boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(2u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr(uint8_t v_x_97_, lean_object* v_prec_98_){
_start:
{
lean_object* v___y_100_; lean_object* v___y_107_; lean_object* v___y_114_; 
switch(v_x_97_)
{
case 0:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = lean_nat_dec_le(v___x_120_, v_prec_98_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_100_ = v___x_122_;
goto v___jp_99_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_100_ = v___x_123_;
goto v___jp_99_;
}
}
case 1:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1024u);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_prec_98_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_107_ = v___x_126_;
goto v___jp_106_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_107_ = v___x_127_;
goto v___jp_106_;
}
}
default: 
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1024u);
v___x_129_ = lean_nat_dec_le(v___x_128_, v_prec_98_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__6, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__6_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__6);
v___y_114_ = v___x_130_;
goto v___jp_113_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_NormCast_instReprLabel_repr___closed__7, &l_Lean_Meta_NormCast_instReprLabel_repr___closed__7_once, _init_l_Lean_Meta_NormCast_instReprLabel_repr___closed__7);
v___y_114_ = v___x_131_;
goto v___jp_113_;
}
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__1));
lean_inc(v___y_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___y_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
v___x_105_ = l_Repr_addAppParen(v___x_104_, v_prec_98_);
return v___x_105_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__3));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_98_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Lean_Meta_NormCast_instReprLabel_repr___closed__5));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_98_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_instReprLabel_repr___boxed(lean_object* v_x_132_, lean_object* v_prec_133_){
_start:
{
uint8_t v_x_171__boxed_134_; lean_object* v_res_135_; 
v_x_171__boxed_134_ = lean_unbox(v_x_132_);
v_res_135_ = l_Lean_Meta_NormCast_instReprLabel_repr(v_x_171__boxed_134_, v_prec_133_);
lean_dec(v_prec_133_);
return v_res_135_;
}
}
static uint8_t _init_l_Lean_Meta_NormCast_instInhabitedLabel_default(void){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
}
static uint8_t _init_l_Lean_Meta_NormCast_instInhabitedLabel(void){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(lean_object* v_as_140_, size_t v_sz_141_, size_t v_i_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_a_146_; uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_lt(v_i_142_, v_sz_141_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v_b_143_);
return v___x_151_;
}
else
{
lean_object* v_snd_152_; lean_object* v_fst_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_187_; 
v_snd_152_ = lean_ctor_get(v_b_143_, 1);
v_fst_153_ = lean_ctor_get(v_b_143_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v_b_143_);
if (v_isSharedCheck_187_ == 0)
{
v___x_155_ = v_b_143_;
v_isShared_156_ = v_isSharedCheck_187_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_snd_152_);
lean_inc(v_fst_153_);
lean_dec(v_b_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_187_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_array_157_; lean_object* v_start_158_; lean_object* v_stop_159_; uint8_t v___x_160_; 
v_array_157_ = lean_ctor_get(v_snd_152_, 0);
v_start_158_ = lean_ctor_get(v_snd_152_, 1);
v_stop_159_ = lean_ctor_get(v_snd_152_, 2);
v___x_160_ = lean_nat_dec_lt(v_start_158_, v_stop_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; 
if (v_isShared_156_ == 0)
{
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_fst_153_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_snd_152_);
v___x_162_ = v_reuseFailAlloc_164_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
else
{
lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_183_; 
lean_inc(v_stop_159_);
lean_inc(v_start_158_);
lean_inc_ref(v_array_157_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_snd_152_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_184_ = lean_ctor_get(v_snd_152_, 2);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_snd_152_, 1);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_snd_152_, 0);
lean_dec(v_unused_186_);
v___x_166_ = v_snd_152_;
v_isShared_167_ = v_isSharedCheck_183_;
goto v_resetjp_165_;
}
else
{
lean_dec(v_snd_152_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_183_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_168_ = lean_array_fget(v_array_157_, v_start_158_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_start_158_, v___x_169_);
lean_dec(v_start_158_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_170_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_array_157_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_stop_159_);
v___x_172_ = v_reuseFailAlloc_182_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
uint8_t v___x_173_; 
v___x_173_ = lean_unbox(v___x_168_);
lean_dec(v___x_168_);
if (v___x_173_ == 2)
{
lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v_a_174_ = lean_array_uget_borrowed(v_as_140_, v_i_142_);
lean_inc(v_a_174_);
v___x_175_ = lean_array_push(v_fst_153_, v_a_174_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_172_);
lean_ctor_set(v___x_155_, 0, v___x_175_);
v___x_177_ = v___x_155_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
v_a_146_ = v___x_177_;
goto v___jp_145_;
}
}
else
{
lean_object* v___x_180_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_172_);
v___x_180_ = v___x_155_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_153_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_172_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_a_146_ = v___x_180_;
goto v___jp_145_;
}
}
}
}
}
}
}
v___jp_145_:
{
size_t v___x_147_; size_t v___x_148_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_142_, v___x_147_);
v_i_142_ = v___x_148_;
v_b_143_ = v_a_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg___boxed(lean_object* v_as_188_, lean_object* v_sz_189_, lean_object* v_i_190_, lean_object* v_b_191_, lean_object* v___y_192_){
_start:
{
size_t v_sz_boxed_193_; size_t v_i_boxed_194_; lean_object* v_res_195_; 
v_sz_boxed_193_ = lean_unbox_usize(v_sz_189_);
lean_dec(v_sz_189_);
v_i_boxed_194_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_188_, v_sz_boxed_193_, v_i_boxed_194_, v_b_191_);
lean_dec_ref(v_as_188_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0(void){
_start:
{
lean_object* v___x_196_; lean_object* v_dummy_197_; 
v___x_196_ = lean_box(0);
v_dummy_197_ = l_Lean_Expr_sort___override(v___x_196_);
return v_dummy_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs(lean_object* v_e_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = l_Lean_Expr_getAppFn(v_e_200_);
v___x_207_ = 1;
v___x_208_ = lean_box(0);
v___x_209_ = l_Lean_Meta_mkCongrSimp_x3f(v___x_206_, v___x_207_, v___x_208_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_256_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_256_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_256_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_256_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
if (lean_obj_tag(v_a_210_) == 0)
{
lean_object* v_dummy_214_; lean_object* v_nargs_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v_dummy_214_ = lean_obj_once(&l_Lean_Meta_NormCast_getSimpArgs___closed__0, &l_Lean_Meta_NormCast_getSimpArgs___closed__0_once, _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0);
v_nargs_215_ = l_Lean_Expr_getAppNumArgs(v_e_200_);
lean_inc(v_nargs_215_);
v___x_216_ = lean_mk_array(v_nargs_215_, v_dummy_214_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_sub(v_nargs_215_, v___x_217_);
lean_dec(v_nargs_215_);
v___x_219_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_200_, v___x_216_, v___x_218_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_219_);
v___x_221_ = v___x_212_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_object* v_val_223_; lean_object* v_argKinds_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_dummy_229_; lean_object* v_nargs_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; size_t v_sz_236_; size_t v___x_237_; lean_object* v___x_238_; 
lean_del_object(v___x_212_);
v_val_223_ = lean_ctor_get(v_a_210_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v_a_210_, 1);
v_argKinds_224_ = lean_ctor_get(v_val_223_, 2);
lean_inc_ref(v_argKinds_224_);
lean_dec(v_val_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = ((lean_object*)(l_Lean_Meta_NormCast_getSimpArgs___closed__1));
v___x_227_ = lean_array_get_size(v_argKinds_224_);
v___x_228_ = l_Array_toSubarray___redArg(v_argKinds_224_, v___x_225_, v___x_227_);
v_dummy_229_ = lean_obj_once(&l_Lean_Meta_NormCast_getSimpArgs___closed__0, &l_Lean_Meta_NormCast_getSimpArgs___closed__0_once, _init_l_Lean_Meta_NormCast_getSimpArgs___closed__0);
v_nargs_230_ = l_Lean_Expr_getAppNumArgs(v_e_200_);
lean_inc(v_nargs_230_);
v___x_231_ = lean_mk_array(v_nargs_230_, v_dummy_229_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_sub(v_nargs_230_, v___x_232_);
lean_dec(v_nargs_230_);
v___x_234_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_200_, v___x_231_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_226_);
lean_ctor_set(v___x_235_, 1, v___x_228_);
v_sz_236_ = lean_array_size(v___x_234_);
v___x_237_ = ((size_t)0ULL);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v___x_234_, v_sz_236_, v___x_237_, v___x_235_);
lean_dec_ref(v___x_234_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_fst_243_; lean_object* v___x_245_; 
v_fst_243_ = lean_ctor_get(v_a_239_, 0);
lean_inc(v_fst_243_);
lean_dec(v_a_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v_fst_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_fst_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_a_248_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_238_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v_e_200_);
v_a_257_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_209_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_209_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_getSimpArgs___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_NormCast_getSimpArgs(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(lean_object* v_as_272_, size_t v_sz_273_, size_t v_i_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___redArg(v_as_272_, v_sz_273_, v_i_274_, v_b_275_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0___boxed(lean_object* v_as_282_, lean_object* v_sz_283_, lean_object* v_i_284_, lean_object* v_b_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
size_t v_sz_boxed_291_; size_t v_i_boxed_292_; lean_object* v_res_293_; 
v_sz_boxed_291_ = lean_unbox_usize(v_sz_283_);
lean_dec(v_sz_283_);
v_i_boxed_292_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_NormCast_getSimpArgs_spec__0(v_as_282_, v_sz_boxed_291_, v_i_boxed_292_, v_b_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec_ref(v_as_282_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg(lean_object* v_e_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Expr_getAppFn(v_e_294_);
if (lean_obj_tag(v___x_300_) == 4)
{
lean_object* v_declName_301_; lean_object* v___x_302_; 
v_declName_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_declName_301_);
lean_dec_ref_known(v___x_300_, 2);
v___x_302_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_301_, v_a_295_);
lean_dec(v_declName_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_val_304_; lean_object* v_numArgs_305_; lean_object* v_coercee_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_val_304_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v_a_303_, 1);
v_numArgs_305_ = lean_ctor_get(v_val_304_, 0);
lean_inc(v_numArgs_305_);
v_coercee_306_ = lean_ctor_get(v_val_304_, 1);
lean_inc(v_coercee_306_);
lean_dec(v_val_304_);
v___x_307_ = l_Lean_Expr_getAppNumArgs(v_e_294_);
v___x_308_ = lean_nat_dec_le(v_numArgs_305_, v___x_307_);
lean_dec(v_numArgs_305_);
if (v___x_308_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_coercee_306_);
goto v___jp_297_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_309_ = lean_nat_sub(v___x_307_, v_coercee_306_);
lean_dec(v_coercee_306_);
lean_dec(v___x_307_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_sub(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
v___x_312_ = l_Lean_Expr_getRevArg_x21(v_e_294_, v___x_311_);
v___x_313_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___x_312_, v_a_295_);
lean_dec_ref(v___x_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_nat_add(v_a_314_, v___x_310_);
lean_dec(v_a_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
return v___x_313_;
}
}
}
else
{
lean_dec(v_a_303_);
goto v___jp_297_;
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_a_323_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_302_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_302_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_dec_ref(v___x_300_);
goto v___jp_297_;
}
v___jp_297_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___redArg___boxed(lean_object* v_e_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_e_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes(lean_object* v_e_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_335_, v_a_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countHeadCoes___boxed(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_NormCast_countHeadCoes(v_e_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(lean_object* v_k_349_, lean_object* v_b_350_, lean_object* v_c_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_357_ = lean_apply_7(v_k_349_, v_b_350_, v_c_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed(lean_object* v_k_358_, lean_object* v_b_359_, lean_object* v_c_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0(v_k_358_, v_b_359_, v_c_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(lean_object* v_e_367_, lean_object* v_k_368_, uint8_t v_cleanupAnnotations_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___f_375_; uint8_t v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___f_375_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_375_, 0, v_k_368_);
v___x_376_ = 1;
v___x_377_ = 0;
v___x_378_ = lean_box(0);
v___x_379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_367_, v___x_376_, v___x_377_, v___x_376_, v___x_377_, v___x_378_, v___f_375_, v_cleanupAnnotations_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_379_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_379_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___boxed(lean_object* v_e_396_, lean_object* v_k_397_, lean_object* v_cleanupAnnotations_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_404_; lean_object* v_res_405_; 
v_cleanupAnnotations_boxed_404_ = lean_unbox(v_cleanupAnnotations_398_);
v_res_405_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_396_, v_k_397_, v_cleanupAnnotations_boxed_404_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(lean_object* v_00_u03b1_406_, lean_object* v_e_407_, lean_object* v_k_408_, uint8_t v_cleanupAnnotations_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_407_, v_k_408_, v_cleanupAnnotations_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___boxed(lean_object* v_00_u03b1_416_, lean_object* v_e_417_, lean_object* v_k_418_, lean_object* v_cleanupAnnotations_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_425_; lean_object* v_res_426_; 
v_cleanupAnnotations_boxed_425_ = lean_unbox(v_cleanupAnnotations_419_);
v_res_426_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3(v_00_u03b1_416_, v_e_417_, v_k_418_, v_cleanupAnnotations_boxed_425_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_, lean_object* v_b_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; 
v___x_432_ = lean_array_uget_borrowed(v_as_427_, v_i_428_);
v___x_433_ = lean_nat_add(v_b_430_, v___x_432_);
lean_dec(v_b_430_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_428_, v___x_434_);
v_i_428_ = v___x_435_;
v_b_430_ = v___x_433_;
goto _start;
}
else
{
return v_b_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1___boxed(lean_object* v_as_437_, lean_object* v_i_438_, lean_object* v_stop_439_, lean_object* v_b_440_){
_start:
{
size_t v_i_boxed_441_; size_t v_stop_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_441_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_stop_boxed_442_ = lean_unbox_usize(v_stop_439_);
lean_dec(v_stop_439_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_as_437_, v_i_boxed_441_, v_stop_boxed_442_, v_b_440_);
lean_dec_ref(v_as_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(size_t v_sz_444_, size_t v_i_445_, lean_object* v_bs_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_lt(v_i_445_, v_sz_444_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_bs_446_);
return v___x_453_;
}
else
{
lean_object* v_v_454_; lean_object* v___x_455_; 
v_v_454_ = lean_array_uget_borrowed(v_bs_446_, v_i_445_);
lean_inc(v_v_454_);
v___x_455_ = l_Lean_Meta_NormCast_countCoes(v_v_454_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v_bs_x27_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = lean_unsigned_to_nat(0u);
v_bs_x27_458_ = lean_array_uset(v_bs_446_, v_i_445_, v___x_457_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_445_, v___x_459_);
v___x_461_ = lean_array_uset(v_bs_x27_458_, v_i_445_, v_a_456_);
v_i_445_ = v___x_460_;
v_bs_446_ = v___x_461_;
goto _start;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_bs_446_);
v_a_463_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_455_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_455_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(lean_object* v_upperBound_471_, lean_object* v___x_472_, lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_nat_dec_lt(v_a_474_, v_upperBound_471_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v_a_474_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_b_475_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = lean_nat_sub(v___x_472_, v_a_474_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_sub(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
v___x_486_ = l_Lean_Expr_getRevArg_x21(v_e_473_, v___x_485_);
v___x_487_ = l_Lean_Meta_NormCast_countCoes(v___x_486_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_nat_add(v_b_475_, v_a_488_);
lean_dec(v_a_488_);
lean_dec(v_b_475_);
v___x_490_ = lean_nat_add(v_a_474_, v___x_484_);
lean_dec(v_a_474_);
v_a_474_ = v___x_490_;
v_b_475_ = v___x_489_;
goto _start;
}
else
{
lean_dec(v_b_475_);
lean_dec(v_a_474_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0(lean_object* v_x_492_, lean_object* v_e_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Expr_getAppFn(v_e_493_);
if (lean_obj_tag(v___x_546_) == 4)
{
lean_object* v_declName_547_; lean_object* v___x_548_; 
v_declName_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_declName_547_);
lean_dec_ref_known(v___x_546_, 2);
v___x_548_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_547_, v___y_497_);
lean_dec(v_declName_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
if (lean_obj_tag(v_a_549_) == 1)
{
lean_object* v_val_550_; lean_object* v_numArgs_551_; lean_object* v_coercee_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_val_550_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_a_549_, 1);
v_numArgs_551_ = lean_ctor_get(v_val_550_, 0);
lean_inc(v_numArgs_551_);
v_coercee_552_ = lean_ctor_get(v_val_550_, 1);
lean_inc(v_coercee_552_);
lean_dec(v_val_550_);
v___x_553_ = l_Lean_Expr_getAppNumArgs(v_e_493_);
v___x_554_ = lean_nat_dec_le(v_numArgs_551_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec(v___x_553_);
lean_dec(v_coercee_552_);
lean_dec(v_numArgs_551_);
goto v___jp_499_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = lean_nat_sub(v___x_553_, v_coercee_552_);
lean_dec(v_coercee_552_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_sub(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
v___x_558_ = l_Lean_Expr_getRevArg_x21(v_e_493_, v___x_557_);
v___x_559_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___x_558_, v___y_497_);
lean_dec_ref(v___x_558_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_nat_add(v_a_560_, v___x_556_);
lean_dec(v_a_560_);
v___x_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v___x_553_, v___x_553_, v_e_493_, v_numArgs_551_, v___x_561_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec_ref(v_e_493_);
lean_dec(v___x_553_);
return v___x_562_;
}
else
{
lean_dec(v___x_553_);
lean_dec(v_numArgs_551_);
lean_dec_ref(v_e_493_);
return v___x_559_;
}
}
}
else
{
lean_dec(v_a_549_);
goto v___jp_499_;
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec_ref(v_e_493_);
v_a_563_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_548_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_548_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_dec_ref(v___x_546_);
goto v___jp_499_;
}
v___jp_499_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_NormCast_getSimpArgs(v_e_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_sz_502_ = lean_array_size(v_a_501_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_502_, v___x_503_, v_a_501_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_529_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_529_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_529_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_529_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_array_get_size(v_a_505_);
v___x_511_ = lean_nat_dec_lt(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_509_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_le(v___x_510_, v___x_510_);
if (v___x_515_ == 0)
{
if (v___x_511_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_517_ = v___x_507_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_509_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
size_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_usize_of_nat(v___x_510_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_505_, v___x_503_, v___x_519_, v___x_509_);
lean_dec(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_520_);
v___x_522_ = v___x_507_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = lean_usize_of_nat(v___x_510_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_NormCast_countCoes_spec__1(v_a_505_, v___x_503_, v___x_524_, v___x_509_);
lean_dec(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_525_);
v___x_527_ = v___x_507_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
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
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_504_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_504_);
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
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_a_538_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_500_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_500_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___lam__0___boxed(lean_object* v_x_571_, lean_object* v_e_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Meta_NormCast_countCoes___lam__0(v_x_571_, v_e_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_x_571_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes(lean_object* v_e_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___f_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Meta_NormCast_countCoes___lam__0___boxed), 7, 0);
v___x_586_ = 0;
v___x_587_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg(v_e_579_, v___f_585_, v___x_586_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countCoes___boxed(lean_object* v_e_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_NormCast_countCoes(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg___boxed(lean_object* v_upperBound_595_, lean_object* v___x_596_, lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_595_, v___x_596_, v_e_597_, v_a_598_, v_b_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v_e_597_);
lean_dec(v___x_596_);
lean_dec(v_upperBound_595_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0___boxed(lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_bs_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
size_t v_sz_boxed_614_; size_t v_i_boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_615_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_NormCast_countCoes_spec__0(v_sz_boxed_614_, v_i_boxed_615_, v_bs_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(lean_object* v_upperBound_617_, lean_object* v___x_618_, lean_object* v_e_619_, lean_object* v_inst_620_, lean_object* v_R_621_, lean_object* v_a_622_, lean_object* v_b_623_, lean_object* v_c_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___redArg(v_upperBound_617_, v___x_618_, v_e_619_, v_a_622_, v_b_623_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2___boxed(lean_object* v_upperBound_631_, lean_object* v___x_632_, lean_object* v_e_633_, lean_object* v_inst_634_, lean_object* v_R_635_, lean_object* v_a_636_, lean_object* v_b_637_, lean_object* v_c_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_NormCast_countCoes_spec__2(v_upperBound_631_, v___x_632_, v_e_633_, v_inst_634_, v_R_635_, v_a_636_, v_b_637_, v_c_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_e_633_);
lean_dec(v___x_632_);
lean_dec(v_upperBound_631_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes(lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; 
lean_inc_ref(v_e_645_);
v___x_651_ = l_Lean_Meta_NormCast_countCoes(v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v_e_645_, v_a_649_);
lean_dec_ref(v_e_645_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_662_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = lean_nat_sub(v_a_652_, v_a_654_);
lean_dec(v_a_654_);
lean_dec(v_a_652_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_dec(v_a_652_);
return v___x_653_;
}
}
else
{
lean_dec_ref(v_e_645_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_countInternalCoes___boxed(lean_object* v_e_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_NormCast_countInternalCoes(v_e_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(lean_object* v_type_670_, lean_object* v_k_671_, uint8_t v_cleanupAnnotations_672_, uint8_t v_whnfType_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___f_679_; lean_object* v___x_680_; 
v___f_679_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_NormCast_countCoes_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_679_, 0, v_k_671_);
v___x_680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_670_, v___f_679_, v_cleanupAnnotations_672_, v_whnfType_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
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
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg___boxed(lean_object* v_type_697_, lean_object* v_k_698_, lean_object* v_cleanupAnnotations_699_, lean_object* v_whnfType_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_706_; uint8_t v_whnfType_boxed_707_; lean_object* v_res_708_; 
v_cleanupAnnotations_boxed_706_ = lean_unbox(v_cleanupAnnotations_699_);
v_whnfType_boxed_707_ = lean_unbox(v_whnfType_700_);
v_res_708_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_697_, v_k_698_, v_cleanupAnnotations_boxed_706_, v_whnfType_boxed_707_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(lean_object* v_00_u03b1_709_, lean_object* v_type_710_, lean_object* v_k_711_, uint8_t v_cleanupAnnotations_712_, uint8_t v_whnfType_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_type_710_, v_k_711_, v_cleanupAnnotations_712_, v_whnfType_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___boxed(lean_object* v_00_u03b1_720_, lean_object* v_type_721_, lean_object* v_k_722_, lean_object* v_cleanupAnnotations_723_, lean_object* v_whnfType_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_730_; uint8_t v_whnfType_boxed_731_; lean_object* v_res_732_; 
v_cleanupAnnotations_boxed_730_ = lean_unbox(v_cleanupAnnotations_723_);
v_whnfType_boxed_731_ = lean_unbox(v_whnfType_724_);
v_res_732_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1(v_00_u03b1_720_, v_type_721_, v_k_722_, v_cleanupAnnotations_boxed_730_, v_whnfType_boxed_731_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v_env_740_; lean_object* v___x_741_; lean_object* v_mctx_742_; lean_object* v_lctx_743_; lean_object* v_options_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_739_ = lean_st_ref_get(v___y_737_);
v_env_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_env_740_);
lean_dec(v___x_739_);
v___x_741_ = lean_st_ref_get(v___y_735_);
v_mctx_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_ref(v_mctx_742_);
lean_dec(v___x_741_);
v_lctx_743_ = lean_ctor_get(v___y_734_, 2);
v_options_744_ = lean_ctor_get(v___y_736_, 1);
lean_inc_ref(v_options_744_);
lean_inc_ref(v_lctx_743_);
v___x_745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_745_, 0, v_env_740_);
lean_ctor_set(v___x_745_, 1, v_mctx_742_);
lean_ctor_set(v___x_745_, 2, v_lctx_743_);
lean_ctor_set(v___x_745_, 3, v_options_744_);
v___x_746_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_msgData_733_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0___boxed(lean_object* v_msgData_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msgData_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(lean_object* v_msg_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_ref_761_; lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_ref_761_ = lean_ctor_get(v___y_758_, 4);
v___x_762_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0_spec__0(v_msg_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc(v_ref_761_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_761_);
lean_ctor_set(v___x_767_, 1, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg___boxed(lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__0));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__2));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__4));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__5, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__5_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__5);
v___x_789_ = l_Lean_MessageData_note(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__7));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__13));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0(lean_object* v_x_802_, lean_object* v_ty_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___y_810_; lean_object* v___x_817_; 
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
v___x_817_ = lean_whnf(v_ty_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_929_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__10));
v___x_930_ = lean_unsigned_to_nat(3u);
v___x_931_ = l_Lean_Expr_isAppOfArity(v_a_818_, v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___lam__0___closed__12));
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_934_ = l_Lean_Expr_isAppOfArity(v_a_818_, v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v___x_935_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__14, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__14_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__14);
v___x_936_ = l_Lean_indentExpr(v_a_818_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_937_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_947_ = l_Lean_Expr_getAppNumArgs(v_a_818_);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_sub(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
lean_inc(v___x_949_);
v___x_950_ = l_Lean_Expr_getRevArg_x21(v_a_818_, v___x_949_);
v___x_951_ = lean_nat_sub(v___x_949_, v___x_948_);
lean_dec(v___x_949_);
v___x_952_ = l_Lean_Expr_getRevArg_x21(v_a_818_, v___x_951_);
v_fst_897_ = v___x_950_;
v_snd_898_ = v___x_952_;
v___y_899_ = v___y_804_;
v___y_900_ = v___y_805_;
v___y_901_ = v___y_806_;
v___y_902_ = v___y_807_;
goto v___jp_896_;
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = l_Lean_Expr_getAppNumArgs(v_a_818_);
v___x_955_ = lean_nat_sub(v___x_954_, v___x_953_);
v___x_956_ = lean_nat_sub(v___x_955_, v___x_953_);
lean_dec(v___x_955_);
v___x_957_ = l_Lean_Expr_getRevArg_x21(v_a_818_, v___x_956_);
v___x_958_ = lean_unsigned_to_nat(2u);
v___x_959_ = lean_nat_sub(v___x_954_, v___x_958_);
lean_dec(v___x_954_);
v___x_960_ = lean_nat_sub(v___x_959_, v___x_953_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_Expr_getRevArg_x21(v_a_818_, v___x_960_);
v_fst_897_ = v___x_957_;
v_snd_898_ = v___x_961_;
v___y_899_ = v___y_804_;
v___y_900_ = v___y_805_;
v___y_901_ = v___y_806_;
v___y_902_ = v___y_807_;
goto v___jp_896_;
}
v___jp_819_:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_820_, v___y_826_);
lean_dec_ref(v___y_820_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = l_Lean_Meta_NormCast_countHeadCoes___redArg(v___y_821_, v___y_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
lean_inc_ref(v___y_821_);
v___x_831_ = l_Lean_Meta_NormCast_countInternalCoes(v___y_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_871_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_871_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_871_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_871_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_nat_dec_eq(v_a_828_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_dec_eq(v_a_828_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
lean_dec(v_a_832_);
lean_dec_ref(v___y_821_);
v___x_840_ = lean_nat_dec_lt(v_a_830_, v_a_828_);
lean_dec(v_a_828_);
lean_dec(v_a_830_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_834_);
v___x_841_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__1, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__1_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__1);
v___x_842_ = l_Lean_indentExpr(v_a_818_);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_inc_ref(v___y_822_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v___y_822_);
v___x_845_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_844_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_845_;
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_a_818_);
v___x_846_ = 2;
v___x_847_ = lean_box(v___x_846_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_847_);
v___x_849_ = v___x_834_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
uint8_t v___x_851_; uint8_t v___x_852_; 
lean_del_object(v___x_834_);
lean_dec(v_a_828_);
lean_dec(v_a_818_);
v___x_851_ = lean_nat_dec_eq(v_a_832_, v___x_836_);
lean_dec(v_a_832_);
v___x_852_ = lean_nat_dec_eq(v_a_830_, v___x_836_);
lean_dec(v_a_830_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v___x_853_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__3, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__3_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__3);
v___x_854_ = l_Lean_indentExpr(v___y_821_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_inc_ref(v___y_822_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___y_822_);
v___x_857_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_856_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_dec_ref(v___y_821_);
v___y_810_ = v___x_851_;
goto v___jp_809_;
}
}
}
else
{
uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_dec(v_a_832_);
lean_dec(v_a_830_);
lean_dec(v_a_828_);
lean_dec_ref(v___y_821_);
lean_dec(v_a_818_);
v___x_866_ = 0;
v___x_867_ = lean_box(v___x_866_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_867_);
v___x_869_ = v___x_834_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_830_);
lean_dec(v_a_828_);
lean_dec_ref(v___y_821_);
lean_dec(v_a_818_);
v_a_872_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_831_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_831_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_a_828_);
lean_dec_ref(v___y_821_);
lean_dec(v_a_818_);
v_a_880_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_829_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_829_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v___y_821_);
lean_dec(v_a_818_);
v_a_888_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_827_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_827_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_903_; 
lean_inc_ref(v_fst_897_);
v___x_903_ = l_Lean_Meta_NormCast_countCoes(v_fst_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__6, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__6_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__6);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v_a_904_, v___x_906_);
lean_dec(v_a_904_);
if (v___x_907_ == 0)
{
v___y_820_ = v_fst_897_;
v___y_821_ = v_snd_898_;
v___y_822_ = v___x_905_;
v___y_823_ = v___y_899_;
v___y_824_ = v___y_900_;
v___y_825_ = v___y_901_;
v___y_826_ = v___y_902_;
goto v___jp_819_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_snd_898_);
lean_dec(v_a_818_);
v___x_908_ = lean_obj_once(&l_Lean_Meta_NormCast_classifyType___lam__0___closed__8, &l_Lean_Meta_NormCast_classifyType___lam__0___closed__8_once, _init_l_Lean_Meta_NormCast_classifyType___lam__0___closed__8);
v___x_909_ = l_Lean_indentExpr(v_fst_897_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_905_);
v___x_912_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v___x_911_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_snd_898_);
lean_dec_ref(v_fst_897_);
lean_dec(v_a_818_);
v_a_921_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_903_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_903_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_817_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_817_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
v___jp_809_:
{
if (v___y_810_ == 0)
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 1;
v___x_812_ = lean_box(v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
else
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = 2;
v___x_815_ = lean_box(v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___lam__0___boxed(lean_object* v_x_970_, lean_object* v_ty_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_NormCast_classifyType___lam__0(v_x_970_, v_ty_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v_x_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType(lean_object* v_ty_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___f_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v___f_985_ = ((lean_object*)(l_Lean_Meta_NormCast_classifyType___closed__0));
v___x_986_ = 0;
v___x_987_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_NormCast_classifyType_spec__1___redArg(v_ty_979_, v___f_985_, v___x_986_, v___x_986_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_classifyType___boxed(lean_object* v_ty_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Meta_NormCast_classifyType(v_ty_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(lean_object* v_00_u03b1_995_, lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0(v_00_u03b1_1003_, v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_));
v___x_1028_ = l_Lean_Meta_registerSimpAttr(v___x_1025_, v___x_1026_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2____boxed(lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1498661328____hygCtx___hyg_2_();
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Lean_Meta_instInhabitedSimpEntry_default;
v___x_1032_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__0);
v___x_1034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
lean_ctor_set(v___x_1034_, 2, v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default(void){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1, &l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1_once, _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default___closed__1);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Meta_NormCast_instInhabitedNormCastExtension(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Meta_NormCast_instInhabitedNormCastExtension_default;
return v___x_1036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1048_ = l_Lean_Name_append(v___x_1047_, v___x_1046_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1054_ = l_Lean_Name_append(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1060_ = l_Lean_Name_append(v___x_1059_, v___x_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1063_ = l_Lean_Meta_mkSimpExt(v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1066_ = l_Lean_Meta_mkSimpExt(v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__10_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_);
v___x_1069_ = l_Lean_Meta_mkSimpExt(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1064_);
lean_ctor_set(v___x_1074_, 1, v_a_1067_);
lean_ctor_set(v___x_1074_, 2, v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1067_);
lean_dec(v_a_1064_);
v_a_1079_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1069_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1064_);
v_a_1087_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1066_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1066_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1063_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1063_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2____boxed(lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_();
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim(lean_object* v_decl_1105_, uint8_t v_kind_1106_, lean_object* v_prio_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_up_1114_; uint8_t v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1113_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1114_ = lean_ctor_get(v___x_1113_, 0);
v___x_1115_ = 1;
v___x_1116_ = 0;
lean_inc_ref(v_up_1114_);
v___x_1117_ = l_Lean_Meta_addSimpTheorem(v_up_1114_, v_decl_1105_, v___x_1115_, v___x_1116_, v_kind_1106_, v_prio_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addElim___boxed(lean_object* v_decl_1118_, lean_object* v_kind_1119_, lean_object* v_prio_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
uint8_t v_kind_boxed_1126_; lean_object* v_res_1127_; 
v_kind_boxed_1126_ = lean_unbox(v_kind_1119_);
v_res_1127_ = l_Lean_Meta_NormCast_addElim(v_decl_1118_, v_kind_boxed_1126_, v_prio_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove(lean_object* v_decl_1128_, uint8_t v_kind_1129_, lean_object* v_prio_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1137_ = 1;
v___x_1138_ = 0;
lean_inc(v_prio_1130_);
lean_inc(v_decl_1128_);
v___x_1139_ = l_Lean_Meta_addSimpTheorem(v___x_1136_, v_decl_1128_, v___x_1137_, v___x_1138_, v_kind_1129_, v_prio_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; lean_object* v_up_1141_; lean_object* v_down_1142_; lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1139_, 1);
v___x_1140_ = l_Lean_Meta_NormCast_normCastExt;
v_up_1141_ = lean_ctor_get(v___x_1140_, 0);
v_down_1142_ = lean_ctor_get(v___x_1140_, 1);
lean_inc(v_prio_1130_);
lean_inc(v_decl_1128_);
lean_inc_ref(v_up_1141_);
v___x_1143_ = l_Lean_Meta_addSimpTheorem(v_up_1141_, v_decl_1128_, v___x_1137_, v___x_1137_, v_kind_1129_, v_prio_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref_known(v___x_1143_, 1);
lean_inc_ref(v_down_1142_);
v___x_1144_ = l_Lean_Meta_addSimpTheorem(v_down_1142_, v_decl_1128_, v___x_1137_, v___x_1138_, v_kind_1129_, v_prio_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1144_;
}
else
{
lean_dec(v_prio_1130_);
lean_dec(v_decl_1128_);
return v___x_1143_;
}
}
else
{
lean_dec(v_prio_1130_);
lean_dec(v_decl_1128_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addMove___boxed(lean_object* v_decl_1145_, lean_object* v_kind_1146_, lean_object* v_prio_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
uint8_t v_kind_boxed_1153_; lean_object* v_res_1154_; 
v_kind_boxed_1153_ = lean_unbox(v_kind_1146_);
v_res_1154_ = l_Lean_Meta_NormCast_addMove(v_decl_1145_, v_kind_boxed_1153_, v_prio_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash(lean_object* v_decl_1155_, uint8_t v_kind_1156_, lean_object* v_prio_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1163_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_1164_ = 1;
v___x_1165_ = 0;
lean_inc(v_prio_1157_);
lean_inc(v_decl_1155_);
v___x_1166_ = l_Lean_Meta_addSimpTheorem(v___x_1163_, v_decl_1155_, v___x_1164_, v___x_1165_, v_kind_1156_, v_prio_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1167_; lean_object* v_down_1168_; lean_object* v_squash_1169_; lean_object* v___x_1170_; 
lean_dec_ref_known(v___x_1166_, 1);
v___x_1167_ = l_Lean_Meta_NormCast_normCastExt;
v_down_1168_ = lean_ctor_get(v___x_1167_, 1);
v_squash_1169_ = lean_ctor_get(v___x_1167_, 2);
lean_inc(v_prio_1157_);
lean_inc(v_decl_1155_);
lean_inc_ref(v_squash_1169_);
v___x_1170_ = l_Lean_Meta_addSimpTheorem(v_squash_1169_, v_decl_1155_, v___x_1164_, v___x_1165_, v_kind_1156_, v_prio_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v___x_1170_, 1);
lean_inc_ref(v_down_1168_);
v___x_1171_ = l_Lean_Meta_addSimpTheorem(v_down_1168_, v_decl_1155_, v___x_1164_, v___x_1165_, v_kind_1156_, v_prio_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1171_;
}
else
{
lean_dec(v_prio_1157_);
lean_dec(v_decl_1155_);
return v___x_1170_;
}
}
else
{
lean_dec(v_prio_1157_);
lean_dec(v_decl_1155_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addSquash___boxed(lean_object* v_decl_1172_, lean_object* v_kind_1173_, lean_object* v_prio_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
uint8_t v_kind_boxed_1180_; lean_object* v_res_1181_; 
v_kind_boxed_1180_ = lean_unbox(v_kind_1173_);
v_res_1181_ = l_Lean_Meta_NormCast_addSquash(v_decl_1172_, v_kind_boxed_1180_, v_prio_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
return v_res_1181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_ctor_set(v___x_1187_, 2, v___x_1186_);
lean_ctor_set(v___x_1187_, 3, v___x_1186_);
lean_ctor_set(v___x_1187_, 4, v___x_1185_);
lean_ctor_set(v___x_1187_, 5, v___x_1185_);
lean_ctor_set(v___x_1187_, 6, v___x_1185_);
lean_ctor_set(v___x_1187_, 7, v___x_1185_);
lean_ctor_set(v___x_1187_, 8, v___x_1185_);
lean_ctor_set(v___x_1187_, 9, v___x_1185_);
lean_ctor_set(v___x_1187_, 10, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(32u);
v___x_1189_ = lean_mk_empty_array_with_capacity(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1191_ = ((size_t)5ULL);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_unsigned_to_nat(32u);
v___x_1194_ = lean_mk_empty_array_with_capacity(v___x_1193_);
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1196_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
lean_ctor_set(v___x_1196_, 2, v___x_1192_);
lean_ctor_set(v___x_1196_, 3, v___x_1192_);
lean_ctor_set_usize(v___x_1196_, 4, v___x_1191_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_box(1);
v___x_1198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
lean_ctor_set(v___x_1200_, 2, v___x_1197_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1203_ = l_Lean_stringToMessageData(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1222_, lean_object* v_declHint_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; uint8_t v___x_1228_; 
v___x_1226_ = lean_st_ref_get(v___y_1224_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = l_Lean_Name_isAnonymous(v_declHint_1223_);
if (v___x_1228_ == 0)
{
uint8_t v_isExporting_1229_; 
v_isExporting_1229_ = lean_ctor_get_uint8(v_env_1227_, sizeof(void*)*8);
if (v_isExporting_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v_env_1227_);
lean_dec(v_declHint_1223_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_msg_1222_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
lean_inc_ref(v_env_1227_);
v___x_1231_ = l_Lean_Environment_setExporting(v_env_1227_, v___x_1228_);
lean_inc(v_declHint_1223_);
lean_inc_ref(v___x_1231_);
v___x_1232_ = l_Lean_Environment_contains(v___x_1231_, v_declHint_1223_, v_isExporting_1229_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_env_1227_);
lean_dec(v_declHint_1223_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_msg_1222_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_c_1239_; lean_object* v___x_1240_; 
v___x_1234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1236_ = l_Lean_Options_empty;
v___x_1237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1234_);
lean_ctor_set(v___x_1237_, 2, v___x_1235_);
lean_ctor_set(v___x_1237_, 3, v___x_1236_);
lean_inc(v_declHint_1223_);
v___x_1238_ = l_Lean_MessageData_ofConstName(v_declHint_1223_, v___x_1228_);
v_c_1239_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1239_, 0, v___x_1237_);
lean_ctor_set(v_c_1239_, 1, v___x_1238_);
v___x_1240_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1227_, v_declHint_1223_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v_env_1227_);
lean_dec(v_declHint_1223_);
v___x_1241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_c_1239_);
v___x_1243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_MessageData_note(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_msg_1222_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1283_; 
v_val_1248_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1250_ = v___x_1240_;
v_isShared_1251_ = v_isSharedCheck_1283_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_val_1248_);
lean_dec(v___x_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1283_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_mod_1255_; uint8_t v___x_1256_; 
v___x_1252_ = lean_box(0);
v___x_1253_ = l_Lean_Environment_header(v_env_1227_);
lean_dec_ref(v_env_1227_);
v___x_1254_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1253_);
v_mod_1255_ = lean_array_get(v___x_1252_, v___x_1254_, v_val_1248_);
lean_dec(v_val_1248_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = l_Lean_isPrivateName(v_declHint_1223_);
lean_dec(v_declHint_1223_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_c_1239_);
v___x_1259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_MessageData_ofName(v_mod_1255_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_MessageData_note(v___x_1264_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_msg_1222_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1266_);
v___x_1268_ = v___x_1250_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_c_1239_);
v___x_1272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_MessageData_ofName(v_mod_1255_);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_MessageData_note(v___x_1277_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_msg_1222_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1279_);
v___x_1281_ = v___x_1250_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1284_; 
lean_dec_ref(v_env_1227_);
lean_dec(v_declHint_1223_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_msg_1222_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1285_, lean_object* v_declHint_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1285_, v_declHint_1286_, v___y_1287_);
lean_dec(v___y_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1290_, lean_object* v_declHint_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
v___x_1297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1290_, v_declHint_1291_, v___y_1295_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1302_ = l_Lean_unknownIdentifierMessageTag;
v___x_1303_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v_a_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_toCold_1323_; lean_object* v_options_1324_; lean_object* v_currRecDepth_1325_; lean_object* v_maxRecDepth_1326_; lean_object* v_ref_1327_; lean_object* v_currNamespace_1328_; lean_object* v_openDecls_1329_; lean_object* v_initHeartbeats_1330_; lean_object* v_maxHeartbeats_1331_; lean_object* v_currMacroScope_1332_; uint8_t v_diag_1333_; uint8_t v_suppressElabErrors_1334_; lean_object* v_ref_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_toCold_1323_ = lean_ctor_get(v___y_1320_, 0);
v_options_1324_ = lean_ctor_get(v___y_1320_, 1);
v_currRecDepth_1325_ = lean_ctor_get(v___y_1320_, 2);
v_maxRecDepth_1326_ = lean_ctor_get(v___y_1320_, 3);
v_ref_1327_ = lean_ctor_get(v___y_1320_, 4);
v_currNamespace_1328_ = lean_ctor_get(v___y_1320_, 5);
v_openDecls_1329_ = lean_ctor_get(v___y_1320_, 6);
v_initHeartbeats_1330_ = lean_ctor_get(v___y_1320_, 7);
v_maxHeartbeats_1331_ = lean_ctor_get(v___y_1320_, 8);
v_currMacroScope_1332_ = lean_ctor_get(v___y_1320_, 9);
v_diag_1333_ = lean_ctor_get_uint8(v___y_1320_, sizeof(void*)*10);
v_suppressElabErrors_1334_ = lean_ctor_get_uint8(v___y_1320_, sizeof(void*)*10 + 1);
v_ref_1335_ = l_Lean_replaceRef(v_ref_1316_, v_ref_1327_);
lean_inc(v_currMacroScope_1332_);
lean_inc(v_maxHeartbeats_1331_);
lean_inc(v_initHeartbeats_1330_);
lean_inc(v_openDecls_1329_);
lean_inc(v_currNamespace_1328_);
lean_inc(v_maxRecDepth_1326_);
lean_inc(v_currRecDepth_1325_);
lean_inc_ref(v_options_1324_);
lean_inc_ref(v_toCold_1323_);
v___x_1336_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1336_, 0, v_toCold_1323_);
lean_ctor_set(v___x_1336_, 1, v_options_1324_);
lean_ctor_set(v___x_1336_, 2, v_currRecDepth_1325_);
lean_ctor_set(v___x_1336_, 3, v_maxRecDepth_1326_);
lean_ctor_set(v___x_1336_, 4, v_ref_1335_);
lean_ctor_set(v___x_1336_, 5, v_currNamespace_1328_);
lean_ctor_set(v___x_1336_, 6, v_openDecls_1329_);
lean_ctor_set(v___x_1336_, 7, v_initHeartbeats_1330_);
lean_ctor_set(v___x_1336_, 8, v_maxHeartbeats_1331_);
lean_ctor_set(v___x_1336_, 9, v_currMacroScope_1332_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*10, v_diag_1333_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*10 + 1, v_suppressElabErrors_1334_);
v___x_1337_ = l_Lean_throwError___at___00Lean_Meta_NormCast_classifyType_spec__0___redArg(v_msg_1317_, v___y_1318_, v___y_1319_, v___x_1336_, v___y_1321_);
lean_dec_ref_known(v___x_1336_, 10);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1338_, v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v_ref_1338_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1346_, lean_object* v_msg_1347_, lean_object* v_declHint_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v_a_1355_; lean_object* v___x_1356_; 
v___x_1354_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1347_, v_declHint_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1346_, v_a_1355_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1357_, lean_object* v_msg_1358_, lean_object* v_declHint_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1357_, v_msg_1358_, v_declHint_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v_ref_1357_);
return v_res_1365_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1372_, lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1379_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1380_ = 0;
lean_inc(v_constName_1373_);
v___x_1381_ = l_Lean_MessageData_ofConstName(v_constName_1373_, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1379_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1372_, v___x_1384_, v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1386_, lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1386_, v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v_ref_1386_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(lean_object* v_constName_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_ref_1400_; lean_object* v___x_1401_; 
v_ref_1400_ = lean_ctor_get(v___y_1397_, 4);
v___x_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1400_, v_constName_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(lean_object* v_constName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v_env_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_st_ref_get(v___y_1413_);
v_env_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc_ref(v_env_1416_);
lean_dec(v___x_1415_);
v___x_1417_ = 0;
lean_inc(v_constName_1409_);
v___x_1418_ = l_Lean_Environment_findConstVal_x3f(v_env_1416_, v_constName_1409_, v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_constName_1409_);
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 0);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_val_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0___boxed(lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer(lean_object* v_decl_1435_, uint8_t v_kind_1436_, lean_object* v_prio_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
lean_inc(v_decl_1435_);
v___x_1443_ = l_Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0(v_decl_1435_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v_type_1445_; lean_object* v___x_1446_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v_type_1445_ = lean_ctor_get(v_a_1444_, 2);
lean_inc_ref(v_type_1445_);
lean_dec(v_a_1444_);
v___x_1446_ = l_Lean_Meta_NormCast_classifyType(v_type_1445_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; uint8_t v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = lean_unbox(v_a_1447_);
lean_dec(v_a_1447_);
switch(v___x_1448_)
{
case 0:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Meta_NormCast_addElim(v_decl_1435_, v_kind_1436_, v_prio_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1449_;
}
case 1:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Meta_NormCast_addMove(v_decl_1435_, v_kind_1436_, v_prio_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1450_;
}
default: 
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Meta_NormCast_addSquash(v_decl_1435_, v_kind_1436_, v_prio_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_prio_1437_);
lean_dec(v_decl_1435_);
v_a_1452_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1446_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1446_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_prio_1437_);
lean_dec(v_decl_1435_);
v_a_1460_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1443_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1443_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_NormCast_addInfer___boxed(lean_object* v_decl_1468_, lean_object* v_kind_1469_, lean_object* v_prio_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_kind_boxed_1476_; lean_object* v_res_1477_; 
v_kind_boxed_1476_ = lean_unbox(v_kind_1469_);
v_res_1477_ = l_Lean_Meta_NormCast_addInfer(v_decl_1468_, v_kind_boxed_1476_, v_prio_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(lean_object* v_00_u03b1_1478_, lean_object* v_constName_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___redArg(v_constName_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_constName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0(v_00_u03b1_1486_, v_constName_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___redArg(v_ref_1495_, v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_ref_1504_, lean_object* v_constName_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1(v_00_u03b1_1503_, v_ref_1504_, v_constName_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v_ref_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1512_, lean_object* v_ref_1513_, lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1513_, v_msg_1514_, v_declHint_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1522_, v_ref_1523_, v_msg_1524_, v_declHint_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v_ref_1523_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1532_, lean_object* v_declHint_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1532_, v_declHint_1533_, v___y_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1540_, lean_object* v_declHint_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1540_, v_declHint_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1548_, lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1557_, v_ref_1558_, v_msg_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___f_1573_; lean_object* v___x_958__overap_1574_; lean_object* v___x_1575_; 
v___f_1573_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___closed__0));
v___x_958__overap_1574_ = lean_panic_fn_borrowed(v___f_1573_, v_msg_1567_);
lean_inc(v___y_1571_);
lean_inc_ref(v___y_1570_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
v___x_1575_ = lean_apply_5(v___x_958__overap_1574_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, lean_box(0));
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0___boxed(lean_object* v_msg_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v_msg_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1589_ = lean_unsigned_to_nat(11u);
v___x_1590_ = lean_unsigned_to_nat(165u);
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1593_ = l_mkPanicMessageWithDecl(v___x_1592_, v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1595_ = lean_unsigned_to_nat(71u);
v___x_1596_ = lean_unsigned_to_nat(158u);
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1599_ = l_mkPanicMessageWithDecl(v___x_1598_, v___x_1597_, v___x_1596_, v___x_1595_, v___x_1594_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v_decl_1600_, uint8_t v_kind_1601_, lean_object* v_stx_1602_, lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v_x_1606_, lean_object* v_label_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = l_Lean_Syntax_getArg(v_stx_1602_, v___x_1603_);
v___x_1642_ = l_Lean_Syntax_isNone(v___x_1641_);
if (v___x_1642_ == 0)
{
uint8_t v___x_1643_; 
lean_inc(v___x_1641_);
v___x_1643_ = l_Lean_Syntax_matchesNull(v___x_1641_, v___x_1604_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v___x_1641_);
lean_dec(v_decl_1600_);
v___x_1644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1645_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1644_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1645_;
}
else
{
lean_object* v_prio_1646_; lean_object* v___x_1647_; 
v_prio_1646_ = l_Lean_Syntax_getArg(v___x_1641_, v___x_1605_);
lean_dec(v___x_1641_);
v___x_1647_ = l_Lean_Syntax_isNatLit_x3f(v_prio_1646_);
lean_dec(v_prio_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
v___y_1636_ = v___y_1608_;
v___y_1637_ = v___y_1611_;
v___y_1638_ = v___y_1609_;
v___y_1639_ = v___y_1610_;
goto v___jp_1635_;
}
else
{
lean_object* v_val_1648_; 
v_val_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___y_1614_ = v___y_1608_;
v___y_1615_ = v___y_1611_;
v___y_1616_ = v___y_1609_;
v___y_1617_ = v___y_1610_;
v___y_1618_ = v_val_1648_;
goto v___jp_1613_;
}
}
}
else
{
lean_dec(v___x_1641_);
v___y_1636_ = v___y_1608_;
v___y_1637_ = v___y_1611_;
v___y_1638_ = v___y_1609_;
v___y_1639_ = v___y_1610_;
goto v___jp_1635_;
}
v___jp_1613_:
{
if (lean_obj_tag(v_label_1607_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_NormCast_addInfer(v_decl_1600_, v_kind_1601_, v___y_1618_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_label_1607_, 0);
v___x_1621_ = l_Lean_Syntax_isStrLit_x3f(v_val_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_NormCast_addInfer(v_decl_1600_, v_kind_1601_, v___y_1618_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_val_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1625_ = lean_string_dec_eq(v_val_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1627_ = lean_string_dec_eq(v_val_1623_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1076155456____hygCtx___hyg_2_));
v___x_1629_ = lean_string_dec_eq(v_val_1623_, v___x_1628_);
lean_dec(v_val_1623_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v___y_1618_);
lean_dec(v_decl_1600_);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1631_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1630_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_NormCast_addSquash(v_decl_1600_, v_kind_1601_, v___y_1618_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1632_;
}
}
else
{
lean_object* v___x_1633_; 
lean_dec(v_val_1623_);
v___x_1633_ = l_Lean_Meta_NormCast_addMove(v_decl_1600_, v_kind_1601_, v___y_1618_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1633_;
}
}
else
{
lean_object* v___x_1634_; 
lean_dec(v_val_1623_);
v___x_1634_ = l_Lean_Meta_NormCast_addElim(v_decl_1600_, v_kind_1601_, v___y_1618_, v___y_1614_, v___y_1616_, v___y_1617_, v___y_1615_);
return v___x_1634_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_unsigned_to_nat(1000u);
v___y_1614_ = v___y_1636_;
v___y_1615_ = v___y_1637_;
v___y_1616_ = v___y_1638_;
v___y_1617_ = v___y_1639_;
v___y_1618_ = v___x_1640_;
goto v___jp_1613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_decl_1649_, lean_object* v_kind_1650_, lean_object* v_stx_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, lean_object* v_x_1655_, lean_object* v_label_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_kind_boxed_1662_; lean_object* v_res_1663_; 
v_kind_boxed_1662_ = lean_unbox(v_kind_1650_);
v_res_1663_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1649_, v_kind_boxed_1662_, v_stx_1651_, v___x_1652_, v___x_1653_, v___x_1654_, v_x_1655_, v_label_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_label_1656_);
lean_dec(v___x_1654_);
lean_dec(v___x_1653_);
lean_dec(v___x_1652_);
lean_dec(v_stx_1651_);
return v_res_1663_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1670_; uint64_t v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1671_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1674_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set_uint64(v___x_1674_, sizeof(void*)*1, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1679_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
lean_ctor_set(v___x_1679_, 3, v___x_1678_);
lean_ctor_set(v___x_1679_, 4, v___x_1678_);
lean_ctor_set(v___x_1679_, 5, v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
lean_ctor_set(v___x_1681_, 2, v___x_1680_);
lean_ctor_set(v___x_1681_, 3, v___x_1680_);
lean_ctor_set(v___x_1681_, 4, v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1685_, lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_decl_1690_, lean_object* v_stx_1691_, uint8_t v_kind_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___y_1716_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1696_ = 1;
v___x_1697_ = 0;
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__4_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1700_ = lean_unsigned_to_nat(32u);
v___x_1701_ = lean_mk_empty_array_with_capacity(v___x_1700_);
v___x_1702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1703_ = ((size_t)5ULL);
lean_inc_n(v___x_1685_, 7);
v___x_1704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1701_);
lean_ctor_set(v___x_1704_, 2, v___x_1685_);
lean_ctor_set(v___x_1704_, 3, v___x_1685_);
lean_ctor_set_usize(v___x_1704_, 4, v___x_1703_);
v___x_1705_ = lean_box(1);
lean_inc_ref(v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1699_);
lean_ctor_set(v___x_1706_, 1, v___x_1704_);
lean_ctor_set(v___x_1706_, 2, v___x_1705_);
v___x_1707_ = lean_mk_empty_array_with_capacity(v___x_1685_);
v___x_1708_ = lean_box(0);
lean_inc(v___x_1686_);
v___x_1709_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1709_, 0, v___x_1698_);
lean_ctor_set(v___x_1709_, 1, v___x_1686_);
lean_ctor_set(v___x_1709_, 2, v___x_1706_);
lean_ctor_set(v___x_1709_, 3, v___x_1707_);
lean_ctor_set(v___x_1709_, 4, v___x_1708_);
lean_ctor_set(v___x_1709_, 5, v___x_1685_);
lean_ctor_set(v___x_1709_, 6, v___x_1708_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*7, v___x_1697_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*7 + 1, v___x_1697_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*7 + 2, v___x_1697_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*7 + 3, v___x_1696_);
v___x_1710_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1685_);
lean_ctor_set(v___x_1710_, 1, v___x_1685_);
lean_ctor_set(v___x_1710_, 2, v___x_1685_);
lean_ctor_set(v___x_1710_, 3, v___x_1685_);
lean_ctor_set(v___x_1710_, 4, v___x_1699_);
lean_ctor_set(v___x_1710_, 5, v___x_1699_);
lean_ctor_set(v___x_1710_, 6, v___x_1699_);
lean_ctor_set(v___x_1710_, 7, v___x_1699_);
lean_ctor_set(v___x_1710_, 8, v___x_1699_);
lean_ctor_set(v___x_1710_, 9, v___x_1699_);
lean_ctor_set(v___x_1710_, 10, v___x_1699_);
v___x_1711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__5_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1710_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
lean_ctor_set(v___x_1713_, 2, v___x_1686_);
lean_ctor_set(v___x_1713_, 3, v___x_1704_);
lean_ctor_set(v___x_1713_, 4, v___x_1712_);
v___x_1714_ = lean_st_mk_ref(v___x_1713_);
v___x_1726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__7_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__8_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
lean_inc_ref(v___x_1687_);
v___x_1728_ = l_Lean_Name_mkStr4(v___x_1687_, v___x_1726_, v___x_1727_, v___x_1688_);
lean_inc(v_stx_1691_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_stx_1691_, v___x_1728_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_stx_1691_);
lean_dec(v_decl_1690_);
lean_dec_ref(v___x_1687_);
lean_dec(v___x_1685_);
v___x_1730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1731_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1730_, v___x_1709_, v___x_1714_, v___y_1693_, v___y_1694_);
lean_dec_ref_known(v___x_1709_, 7);
v___y_1716_ = v___x_1731_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = l_Lean_Syntax_getArg(v_stx_1691_, v___x_1732_);
v___x_1734_ = l_Lean_Syntax_isNone(v___x_1733_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; 
lean_inc(v___x_1733_);
v___x_1735_ = l_Lean_Syntax_matchesNull(v___x_1733_, v___x_1732_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v___x_1733_);
lean_dec(v_stx_1691_);
lean_dec(v_decl_1690_);
lean_dec_ref(v___x_1687_);
lean_dec(v___x_1685_);
v___x_1736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1737_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1736_, v___x_1709_, v___x_1714_, v___y_1693_, v___y_1694_);
lean_dec_ref_known(v___x_1709_, 7);
v___y_1716_ = v___x_1737_;
goto v___jp_1715_;
}
else
{
lean_object* v_label_1738_; 
v_label_1738_ = l_Lean_Syntax_getArg(v___x_1733_, v___x_1685_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1___closed__9_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1744_ = l_Lean_Name_mkStr4(v___x_1687_, v___x_1726_, v___x_1727_, v___x_1743_);
lean_inc(v_label_1738_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v_label_1738_, v___x_1744_);
lean_dec(v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_label_1738_);
lean_dec(v_stx_1691_);
lean_dec(v_decl_1690_);
lean_dec(v___x_1685_);
v___x_1746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1747_ = l_panic___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__0(v___x_1746_, v___x_1709_, v___x_1714_, v___y_1693_, v___y_1694_);
lean_dec_ref_known(v___x_1709_, 7);
v___y_1716_ = v___x_1747_;
goto v___jp_1715_;
}
else
{
goto v___jp_1739_;
}
}
else
{
lean_dec_ref(v___x_1687_);
goto v___jp_1739_;
}
v___jp_1739_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_label_1738_);
v___x_1742_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1690_, v_kind_1692_, v_stx_1691_, v___x_1689_, v___x_1732_, v___x_1685_, v___x_1740_, v___x_1741_, v___x_1709_, v___x_1714_, v___y_1693_, v___y_1694_);
lean_dec_ref_known(v___x_1709_, 7);
lean_dec_ref_known(v___x_1741_, 1);
lean_dec(v___x_1685_);
lean_dec(v_stx_1691_);
v___y_1716_ = v___x_1742_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1733_);
lean_dec_ref(v___x_1687_);
v___x_1748_ = lean_box(0);
v___x_1749_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v_decl_1690_, v_kind_1692_, v_stx_1691_, v___x_1689_, v___x_1732_, v___x_1685_, v___x_1748_, v___x_1708_, v___x_1709_, v___x_1714_, v___y_1693_, v___y_1694_);
lean_dec_ref_known(v___x_1709_, 7);
lean_dec(v___x_1685_);
lean_dec(v_stx_1691_);
v___y_1716_ = v___x_1749_;
goto v___jp_1715_;
}
}
v___jp_1715_:
{
if (lean_obj_tag(v___y_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_a_1717_ = lean_ctor_get(v___y_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___y_1716_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v___y_1716_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___y_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_st_ref_get(v___x_1714_);
lean_dec(v___x_1714_);
lean_dec(v___x_1721_);
if (v_isShared_1720_ == 0)
{
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1717_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_dec(v___x_1714_);
return v___y_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v___x_1754_, lean_object* v_decl_1755_, lean_object* v_stx_1756_, lean_object* v_kind_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v_kind_boxed_1761_; lean_object* v_res_1762_; 
v_kind_boxed_1761_ = lean_unbox(v_kind_1757_);
v_res_1762_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1753_, v___x_1754_, v_decl_1755_, v_stx_1756_, v_kind_boxed_1761_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___x_1754_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v_env_1768_; lean_object* v_options_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1767_ = lean_st_ref_get(v___y_1765_);
v_env_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc_ref(v_env_1768_);
lean_dec(v___x_1767_);
v_options_1769_ = lean_ctor_get(v___y_1764_, 1);
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1771_ = lean_unsigned_to_nat(32u);
v___x_1772_ = lean_mk_empty_array_with_capacity(v___x_1771_);
lean_dec_ref(v___x_1772_);
v___x_1773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_NormCast_addInfer_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_1769_);
v___x_1774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1774_, 0, v_env_1768_);
lean_ctor_set(v___x_1774_, 1, v___x_1770_);
lean_ctor_set(v___x_1774_, 2, v___x_1773_);
lean_ctor_set(v___x_1774_, 3, v_options_1769_);
v___x_1775_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v_msgData_1763_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msgData_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_ref_1786_; lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1796_; 
v_ref_1786_ = lean_ctor_get(v___y_1783_, 4);
v___x_1787_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1_spec__1(v_msg_1782_, v___y_1783_, v___y_1784_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1796_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v_ref_1786_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_ref_1786_);
lean_ctor_set(v___x_1792_, 1, v_a_1788_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set_tag(v___x_1790_, 1);
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(lean_object* v___x_1808_, lean_object* v_decl_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1814_ = l_Lean_MessageData_ofName(v___x_1808_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_obj_once(&l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2___closed__3_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v___x_1817_, v___y_1810_, v___y_1811_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v___x_1819_, lean_object* v_decl_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___lam__2_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(v___x_1819_, v_decl_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v_decl_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn___closed__31_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_));
v___x_1911_ = l_Lean_registerBuiltinAttribute(v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2____boxed(lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2_();
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1914_, lean_object* v_msg_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___redArg(v_msg_1915_, v___y_1916_, v___y_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1920_, lean_object* v_msg_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_NormCast_0__Lean_Meta_NormCast_initFn_00___x40_Lean_Meta_Tactic_NormCast_1115639401____hygCtx___hyg_2__spec__1(v_00_u03b1_1920_, v_msg_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1925_;
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
