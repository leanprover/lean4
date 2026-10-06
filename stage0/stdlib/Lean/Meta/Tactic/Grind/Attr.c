// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__66 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__66_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__66_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__67 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__67_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_tag_nat(v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_19_, lean_object* v_k_20_){
_start:
{
switch(lean_obj_tag(v_t_19_))
{
case 0:
{
lean_object* v_k_21_; lean_object* v___x_22_; 
v_k_21_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_k_21_);
lean_dec_ref_known(v_t_19_, 1);
v___x_22_ = lean_apply_1(v_k_20_, v_k_21_);
return v___x_22_;
}
case 1:
{
uint8_t v_eager_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_eager_23_ = lean_ctor_get_uint8(v_t_19_, 0);
lean_dec_ref_known(v_t_19_, 0);
v___x_24_ = lean_box(v_eager_23_);
v___x_25_ = lean_apply_1(v_k_20_, v___x_24_);
return v___x_25_;
}
case 5:
{
lean_object* v_prio_26_; lean_object* v___x_27_; 
v_prio_26_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_prio_26_);
lean_dec_ref_known(v_t_19_, 1);
v___x_27_ = lean_apply_1(v_k_20_, v_prio_26_);
return v___x_27_;
}
case 8:
{
uint8_t v_post_28_; uint8_t v_inv_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_post_28_ = lean_ctor_get_uint8(v_t_19_, 0);
v_inv_29_ = lean_ctor_get_uint8(v_t_19_, 1);
lean_dec_ref_known(v_t_19_, 0);
v___x_30_ = lean_box(v_post_28_);
v___x_31_ = lean_box(v_inv_29_);
v___x_32_ = lean_apply_2(v_k_20_, v___x_30_, v___x_31_);
return v___x_32_;
}
case 10:
{
uint8_t v_fallback_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_fallback_33_ = lean_ctor_get_uint8(v_t_19_, 0);
lean_dec_ref_known(v_t_19_, 0);
v___x_34_ = lean_box(v_fallback_33_);
v___x_35_ = lean_apply_1(v_k_20_, v___x_34_);
return v___x_35_;
}
default: 
{
lean_dec(v_t_19_);
return v_k_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_36_, lean_object* v_ctorIdx_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_k_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_38_, v_k_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_42_, lean_object* v_ctorIdx_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_k_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_42_, v_ctorIdx_43_, v_t_44_, v_h_45_, v_k_46_);
lean_dec(v_ctorIdx_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_48_, lean_object* v_ematch_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_48_, v_ematch_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_ematch_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_52_, v_ematch_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_56_, lean_object* v_cases_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_56_, v_cases_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_cases_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_60_, v_cases_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_64_, lean_object* v_intro_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_64_, v_intro_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_intro_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_68_, v_intro_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_72_, lean_object* v_infer_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_72_, v_infer_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_infer_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_76_, v_infer_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_80_, lean_object* v_ext_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_80_, v_ext_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_ext_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_84_, v_ext_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_88_, lean_object* v_symbol_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_88_, v_symbol_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_symbol_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_92_, v_symbol_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_96_, lean_object* v_inj_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_96_, v_inj_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_inj_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_100_, v_inj_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_104_, lean_object* v_funCC_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_104_, v_funCC_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_funCC_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_108_, v_funCC_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_112_, lean_object* v_norm_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_112_, v_norm_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_norm_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_116_, v_norm_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_120_, lean_object* v_unfold_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_120_, v_unfold_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_unfold_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_124_, v_unfold_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_128_, lean_object* v_homo_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_128_, v_homo_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_homo_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_132_, v_homo_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_136_, lean_object* v_homoPred_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_136_, v_homoPred_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_homoPred_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_140_, v_homoPred_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set(v___x_150_, 3, v___x_149_);
lean_ctor_set(v___x_150_, 4, v___x_148_);
lean_ctor_set(v___x_150_, 5, v___x_148_);
lean_ctor_set(v___x_150_, 6, v___x_148_);
lean_ctor_set(v___x_150_, 7, v___x_148_);
lean_ctor_set(v___x_150_, 8, v___x_148_);
lean_ctor_set(v___x_150_, 9, v___x_148_);
lean_ctor_set(v___x_150_, 10, v___x_148_);
lean_ctor_set(v___x_150_, 11, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_unsigned_to_nat(32u);
v___x_152_ = lean_mk_empty_array_with_capacity(v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_154_ = ((size_t)5ULL);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_unsigned_to_nat(32u);
v___x_157_ = lean_mk_empty_array_with_capacity(v___x_156_);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_155_);
lean_ctor_set(v___x_159_, 3, v___x_155_);
lean_ctor_set_usize(v___x_159_, 4, v___x_154_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_box(1);
v___x_161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; lean_object* v_toCold_169_; lean_object* v_env_170_; lean_object* v_options_171_; uint8_t v___x_172_; lean_object* v_env_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_168_ = lean_st_ref_get(v___y_166_);
v_toCold_169_ = lean_ctor_get(v___y_165_, 0);
v_env_170_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_env_170_);
lean_dec(v___x_168_);
v_options_171_ = lean_ctor_get(v_toCold_169_, 2);
v___x_172_ = 0;
v_env_173_ = l_Lean_Environment_setRecordingDeps(v_env_170_, v___x_172_);
v___x_174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_171_);
v___x_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_176_, 0, v_env_173_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
lean_ctor_set(v___x_176_, 3, v_options_171_);
v___x_177_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_msgData_164_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_ref_188_; lean_object* v___x_189_; lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_ref_188_ = lean_ctor_get(v___y_185_, 2);
v___x_189_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_184_, v___y_185_, v___y_186_);
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_198_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_inc(v_ref_188_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_ref_188_);
lean_ctor_set(v___x_194_, 1, v_a_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 1);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_204_, lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_toCold_209_; lean_object* v_currRecDepth_210_; lean_object* v_ref_211_; uint16_t v_optionFlags_212_; uint8_t v_suppressElabErrors_213_; uint8_t v_isRecordingDeps_214_; lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_toCold_209_ = lean_ctor_get(v___y_206_, 0);
v_currRecDepth_210_ = lean_ctor_get(v___y_206_, 1);
v_ref_211_ = lean_ctor_get(v___y_206_, 2);
v_optionFlags_212_ = lean_ctor_get_uint16(v___y_206_, sizeof(void*)*3);
v_suppressElabErrors_213_ = lean_ctor_get_uint8(v___y_206_, sizeof(void*)*3 + 2);
v_isRecordingDeps_214_ = lean_ctor_get_uint8(v___y_206_, sizeof(void*)*3 + 3);
v_ref_215_ = l_Lean_replaceRef(v_ref_204_, v_ref_211_);
lean_inc(v_currRecDepth_210_);
lean_inc_ref(v_toCold_209_);
v___x_216_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_216_, 0, v_toCold_209_);
lean_ctor_set(v___x_216_, 1, v_currRecDepth_210_);
lean_ctor_set(v___x_216_, 2, v_ref_215_);
lean_ctor_set_uint16(v___x_216_, sizeof(void*)*3, v_optionFlags_212_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*3 + 2, v_suppressElabErrors_213_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*3 + 3, v_isRecordingDeps_214_);
v___x_217_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_205_, v___x_216_, v___y_207_);
lean_dec_ref_known(v___x_216_, 3);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_218_, lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_218_, v_msg_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v_ref_218_);
return v_res_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_406_);
v___x_411_ = l_Lean_Syntax_isOfKind(v_stx_406_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_413_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_416_, v_a_407_, v_a_408_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_Lean_Syntax_getArg(v_stx_406_, v___x_418_);
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_419_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_419_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_419_);
v___x_425_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_419_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_419_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_419_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_419_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_419_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_419_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_419_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_419_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_419_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_419_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_419_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_419_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_419_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_419_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_419_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_419_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_419_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_419_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_419_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
lean_inc(v___x_419_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_419_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v___x_419_);
v___x_466_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_467_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_470_, v_a_407_, v_a_408_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_stx_406_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = l_Lean_Syntax_getArg(v___x_419_, v___x_472_);
lean_dec(v___x_419_);
v___x_474_ = l_Lean_Syntax_isNatLit_x3f(v___x_473_);
if (lean_obj_tag(v___x_474_) == 1)
{
lean_object* v_val_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
lean_dec(v___x_473_);
v_val_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_val_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 5);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_val_475_);
v___x_480_ = v_reuseFailAlloc_482_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_474_);
v___x_484_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__55, &l_Lean_Meta_Grind_getAttrKindCore___closed__55_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55);
v___x_485_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_473_, v___x_484_, v_a_407_, v_a_408_);
lean_dec(v___x_473_);
return v___x_485_;
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_486_ = lean_box(11);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_488_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_488_, 0, v___x_411_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_490_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_490_, 0, v___x_457_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_492_ = lean_box(9);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_Syntax_getArg(v___x_419_, v___x_494_);
lean_inc(v___x_495_);
v___x_496_ = l_Lean_Syntax_matchesNull(v___x_495_, v___x_418_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
lean_inc(v___x_495_);
v___x_497_ = l_Lean_Syntax_matchesNull(v___x_495_, v___x_494_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_495_);
lean_dec(v___x_419_);
v___x_498_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_499_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_502_, v_a_407_, v_a_408_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_504_ = l_Lean_Syntax_getArg(v___x_495_, v___x_418_);
lean_dec(v___x_495_);
v___x_505_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
lean_inc(v___x_504_);
v___x_506_ = l_Lean_Syntax_isOfKind(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_508_ = l_Lean_Syntax_isOfKind(v___x_504_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_419_);
v___x_509_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_510_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_513_, v_a_407_, v_a_408_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_unsigned_to_nat(2u);
v___x_516_ = l_Lean_Syntax_getArg(v___x_419_, v___x_515_);
lean_dec(v___x_419_);
lean_inc(v___x_516_);
v___x_517_ = l_Lean_Syntax_matchesNull(v___x_516_, v___x_418_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Syntax_matchesNull(v___x_516_, v___x_494_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_519_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_520_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_523_, v_a_407_, v_a_408_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v_stx_406_);
v___x_525_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_525_, 0, v___x_517_);
lean_ctor_set_uint8(v___x_525_, 1, v___x_411_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___x_516_);
lean_dec(v_stx_406_);
v___x_527_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_527_, 0, v___x_506_);
lean_ctor_set_uint8(v___x_527_, 1, v___x_506_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
lean_dec(v___x_504_);
v___x_529_ = lean_unsigned_to_nat(2u);
v___x_530_ = l_Lean_Syntax_getArg(v___x_419_, v___x_529_);
lean_dec(v___x_419_);
lean_inc(v___x_530_);
v___x_531_ = l_Lean_Syntax_matchesNull(v___x_530_, v___x_418_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
v___x_532_ = l_Lean_Syntax_matchesNull(v___x_530_, v___x_494_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_533_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_534_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_537_, v_a_407_, v_a_408_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_stx_406_);
v___x_539_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_539_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_539_, 1, v___x_411_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v___x_530_);
lean_dec(v_stx_406_);
v___x_541_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_541_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_541_, 1, v___x_496_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
lean_dec(v___x_495_);
v___x_543_ = lean_unsigned_to_nat(2u);
v___x_544_ = l_Lean_Syntax_getArg(v___x_419_, v___x_543_);
lean_dec(v___x_419_);
lean_inc(v___x_544_);
v___x_545_ = l_Lean_Syntax_matchesNull(v___x_544_, v___x_418_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_Syntax_matchesNull(v___x_544_, v___x_494_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_548_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_551_, v_a_407_, v_a_408_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_stx_406_);
v___x_553_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_553_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_553_, 1, v___x_411_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_544_);
lean_dec(v_stx_406_);
v___x_555_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_555_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_555_, 1, v___x_453_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_557_ = lean_box(7);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_559_ = lean_box(6);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_561_ = lean_box(4);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_563_ = lean_box(2);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_565_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_565_, 0, v___x_411_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_567_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_567_, 0, v___x_441_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_569_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_569_, 0, v___x_411_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_572_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_574_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__64));
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = l_Lean_Syntax_getArg(v___x_419_, v___x_580_);
lean_dec(v___x_419_);
lean_inc(v___x_581_);
v___x_582_ = l_Lean_Syntax_matchesNull(v___x_581_, v___x_418_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_581_);
v___x_584_ = l_Lean_Syntax_matchesNull(v___x_581_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___x_581_);
v___x_585_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_586_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_589_, v_a_407_, v_a_408_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = l_Lean_Syntax_getArg(v___x_581_, v___x_418_);
lean_dec(v___x_581_);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_593_ = l_Lean_Syntax_isOfKind(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_594_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_595_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_598_, v_a_407_, v_a_408_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_stx_406_);
v___x_600_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_600_, 0, v___x_411_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v___x_581_);
lean_dec(v_stx_406_);
v___x_603_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_603_, 0, v___x_429_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(2u);
v___x_607_ = l_Lean_Syntax_getArg(v___x_419_, v___x_606_);
lean_dec(v___x_419_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Syntax_matchesNull(v___x_607_, v___x_418_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_607_);
v___x_610_ = l_Lean_Syntax_matchesNull(v___x_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v___x_607_);
v___x_611_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_612_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_615_, v_a_407_, v_a_408_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_Syntax_getArg(v___x_607_, v___x_418_);
lean_dec(v___x_607_);
v___x_618_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_619_ = l_Lean_Syntax_isOfKind(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_621_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_624_, v_a_407_, v_a_408_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v_stx_406_);
v___x_626_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_626_, 0, v___x_411_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v___x_607_);
lean_dec(v_stx_406_);
v___x_629_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_629_, 0, v___x_427_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = l_Lean_Syntax_getArg(v___x_419_, v___x_632_);
lean_dec(v___x_419_);
lean_inc(v___x_633_);
v___x_634_ = l_Lean_Syntax_matchesNull(v___x_633_, v___x_418_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
lean_inc(v___x_633_);
v___x_635_ = l_Lean_Syntax_matchesNull(v___x_633_, v___x_632_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v___x_633_);
v___x_636_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_637_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_640_, v_a_407_, v_a_408_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_Syntax_getArg(v___x_633_, v___x_418_);
lean_dec(v___x_633_);
v___x_643_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_644_ = l_Lean_Syntax_isOfKind(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_646_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_649_, v_a_407_, v_a_408_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_stx_406_);
v___x_651_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_651_, 0, v___x_411_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v___x_633_);
lean_dec(v_stx_406_);
v___x_654_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_654_, 0, v___x_425_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v___x_419_);
lean_dec(v_stx_406_);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = l_Lean_Syntax_getArg(v___x_419_, v___x_659_);
lean_dec(v___x_419_);
lean_inc(v___x_660_);
v___x_661_ = l_Lean_Syntax_matchesNull(v___x_660_, v___x_418_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; 
lean_inc(v___x_660_);
v___x_662_ = l_Lean_Syntax_matchesNull(v___x_660_, v___x_659_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v___x_660_);
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_664_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_667_, v_a_407_, v_a_408_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = l_Lean_Syntax_getArg(v___x_660_, v___x_418_);
lean_dec(v___x_660_);
v___x_670_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_671_ = l_Lean_Syntax_isOfKind(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_673_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_676_, v_a_407_, v_a_408_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_stx_406_);
v___x_678_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_678_, 0, v___x_411_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___x_660_);
lean_dec(v_stx_406_);
v___x_681_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_681_, 0, v___x_421_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = l_Lean_Syntax_getArg(v___x_419_, v___x_684_);
lean_dec(v___x_419_);
lean_inc(v___x_685_);
v___x_686_ = l_Lean_Syntax_matchesNull(v___x_685_, v___x_418_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
lean_inc(v___x_685_);
v___x_687_ = l_Lean_Syntax_matchesNull(v___x_685_, v___x_684_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v___x_685_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_689_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_692_, v_a_407_, v_a_408_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = l_Lean_Syntax_getArg(v___x_685_, v___x_418_);
lean_dec(v___x_685_);
v___x_695_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_696_ = l_Lean_Syntax_isOfKind(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_698_ = l_Lean_MessageData_ofSyntax(v_stx_406_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_701_, v_a_407_, v_a_408_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_stx_406_);
v___x_703_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_703_, 0, v___x_411_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v___x_685_);
lean_dec(v_stx_406_);
v___x_706_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__67));
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_713_, lean_object* v_msg_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_719_, v_msg_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_725_, lean_object* v_ref_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_726_, v_msg_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_732_, lean_object* v_ref_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_732_, v_ref_733_, v_msg_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_ref_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = l_Lean_Syntax_getArg(v_stx_739_, v___x_743_);
v___x_745_ = l_Lean_Syntax_isNone(v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = l_Lean_Syntax_getArg(v___x_744_, v___x_746_);
lean_dec(v___x_744_);
v___x_748_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_747_, v_a_740_, v_a_741_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v___x_744_);
v___x_749_ = lean_box(3);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_stx_751_);
return v_res_755_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_763_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_762_, v_a_759_, v_a_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_769_, v_a_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_777_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_782_, lean_object* v_b_783_, uint8_t v_kind_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_toCold_788_; lean_object* v_currNamespace_789_; lean_object* v___x_790_; lean_object* v_env_791_; lean_object* v_nextMacroScope_792_; lean_object* v_ngen_793_; lean_object* v_auxDeclNGen_794_; lean_object* v_traceState_795_; lean_object* v_recordedDeps_796_; lean_object* v_messages_797_; lean_object* v_infoState_798_; lean_object* v_snapshotTasks_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_811_; 
v_toCold_788_ = lean_ctor_get(v___y_785_, 0);
v_currNamespace_789_ = lean_ctor_get(v_toCold_788_, 4);
v___x_790_ = lean_st_ref_take(v___y_786_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
v_nextMacroScope_792_ = lean_ctor_get(v___x_790_, 1);
v_ngen_793_ = lean_ctor_get(v___x_790_, 2);
v_auxDeclNGen_794_ = lean_ctor_get(v___x_790_, 3);
v_traceState_795_ = lean_ctor_get(v___x_790_, 4);
v_recordedDeps_796_ = lean_ctor_get(v___x_790_, 6);
v_messages_797_ = lean_ctor_get(v___x_790_, 7);
v_infoState_798_ = lean_ctor_get(v___x_790_, 8);
v_snapshotTasks_799_ = lean_ctor_get(v___x_790_, 9);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_790_, 5);
lean_dec(v_unused_812_);
v___x_801_ = v___x_790_;
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_snapshotTasks_799_);
lean_inc(v_infoState_798_);
lean_inc(v_messages_797_);
lean_inc(v_recordedDeps_796_);
lean_inc(v_traceState_795_);
lean_inc(v_auxDeclNGen_794_);
lean_inc(v_ngen_793_);
lean_inc(v_nextMacroScope_792_);
lean_inc(v_env_791_);
lean_dec(v___x_790_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_803_ = lean_box(0);
lean_inc(v_currNamespace_789_);
v___x_804_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_791_, v_ext_782_, v_b_783_, v_kind_784_, v_currNamespace_789_);
v___x_805_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 5, v___x_805_);
lean_ctor_set(v___x_801_, 0, v___x_804_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_nextMacroScope_792_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_ngen_793_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_auxDeclNGen_794_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_traceState_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 5, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_810_, 6, v_recordedDeps_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 7, v_messages_797_);
lean_ctor_set(v_reuseFailAlloc_810_, 8, v_infoState_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 9, v_snapshotTasks_799_);
v___x_807_ = v_reuseFailAlloc_810_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_st_ref_put(v___y_786_, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_803_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_813_, lean_object* v_b_814_, lean_object* v_kind_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
uint8_t v_kind_boxed_819_; lean_object* v_res_820_; 
v_kind_boxed_819_ = lean_unbox(v_kind_815_);
v_res_820_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_813_, v_b_814_, v_kind_boxed_819_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_821_, lean_object* v_00_u03b2_822_, lean_object* v_00_u03c3_823_, lean_object* v_ext_824_, lean_object* v_b_825_, uint8_t v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_824_, v_b_825_, v_kind_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_00_u03c3_833_, lean_object* v_ext_834_, lean_object* v_b_835_, lean_object* v_kind_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v_kind_boxed_840_; lean_object* v_res_841_; 
v_kind_boxed_840_ = lean_unbox(v_kind_836_);
v_res_841_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_831_, v_00_u03b2_832_, v_00_u03c3_833_, v_ext_834_, v_b_835_, v_kind_boxed_840_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_842_, lean_object* v_declName_843_, uint8_t v_eager_844_, uint8_t v_attrKind_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
lean_inc(v_declName_843_);
v___x_849_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_843_, v_eager_844_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref_known(v___x_849_, 1);
v___x_850_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_850_, 0, v_declName_843_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*1, v_eager_844_);
v___x_851_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_842_, v___x_850_, v_attrKind_845_, v_a_846_, v_a_847_);
return v___x_851_;
}
else
{
lean_dec(v_declName_843_);
lean_dec_ref(v_ext_842_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_852_, lean_object* v_declName_853_, lean_object* v_eager_854_, lean_object* v_attrKind_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_eager_boxed_859_; uint8_t v_attrKind_boxed_860_; lean_object* v_res_861_; 
v_eager_boxed_859_ = lean_unbox(v_eager_854_);
v_attrKind_boxed_860_ = lean_unbox(v_attrKind_855_);
v_res_861_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_852_, v_declName_853_, v_eager_boxed_859_, v_attrKind_boxed_860_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_862_, lean_object* v_declName_863_, uint8_t v_attrKind_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
lean_inc(v_declName_863_);
v___x_868_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_863_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v___x_868_, 0);
lean_dec(v_unused_877_);
v___x_870_ = v___x_868_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_dec(v___x_868_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_declName_863_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_declName_863_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_862_, v___x_873_, v_attrKind_864_, v_a_865_, v_a_866_);
return v___x_874_;
}
}
}
else
{
lean_dec(v_declName_863_);
lean_dec_ref(v_ext_862_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_878_, lean_object* v_declName_879_, lean_object* v_attrKind_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
uint8_t v_attrKind_boxed_884_; lean_object* v_res_885_; 
v_attrKind_boxed_884_ = lean_unbox(v_attrKind_880_);
v_res_885_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_878_, v_declName_879_, v_attrKind_boxed_884_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_886_, lean_object* v_declName_887_, uint8_t v_attrKind_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v_declName_887_);
v___x_893_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_886_, v___x_892_, v_attrKind_888_, v_a_889_, v_a_890_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_894_, lean_object* v_declName_895_, lean_object* v_attrKind_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
uint8_t v_attrKind_boxed_900_; lean_object* v_res_901_; 
v_attrKind_boxed_900_ = lean_unbox(v_attrKind_896_);
v_res_901_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_894_, v_declName_895_, v_attrKind_boxed_900_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_902_, lean_object* v_s_903_){
_start:
{
lean_object* v_casesTypes_904_; lean_object* v_funCC_905_; lean_object* v_ematch_906_; lean_object* v_inj_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_casesTypes_904_ = lean_ctor_get(v_s_903_, 0);
v_funCC_905_ = lean_ctor_get(v_s_903_, 2);
v_ematch_906_ = lean_ctor_get(v_s_903_, 3);
v_inj_907_ = lean_ctor_get(v_s_903_, 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v_s_903_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_s_903_, 1);
lean_dec(v_unused_915_);
v___x_909_ = v_s_903_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_inj_907_);
lean_inc(v_ematch_906_);
lean_inc(v_funCC_905_);
lean_inc(v_casesTypes_904_);
lean_dec(v_s_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_a_902_);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_casesTypes_904_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_a_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_funCC_905_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_ematch_906_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_inj_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_916_, lean_object* v_declName_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_ext_923_; lean_object* v_toEnvExtension_924_; lean_object* v_env_925_; lean_object* v_asyncMode_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v_extThms_929_; lean_object* v___x_930_; 
v___x_921_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_922_ = lean_st_ref_get(v_a_919_);
v_ext_923_ = lean_ctor_get(v_ext_916_, 1);
v_toEnvExtension_924_ = lean_ctor_get(v_ext_923_, 0);
v_env_925_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_env_925_);
lean_dec(v___x_922_);
v_asyncMode_926_ = lean_ctor_get(v_toEnvExtension_924_, 2);
v___x_927_ = 0;
v___x_928_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_921_, v_ext_916_, v_env_925_, v_asyncMode_926_, v___x_927_);
v_extThms_929_ = lean_ctor_get(v___x_928_, 1);
lean_inc_ref(v_extThms_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_929_, v_declName_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_961_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_961_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v_env_937_; lean_object* v_nextMacroScope_938_; lean_object* v_ngen_939_; lean_object* v_auxDeclNGen_940_; lean_object* v_traceState_941_; lean_object* v_recordedDeps_942_; lean_object* v_messages_943_; lean_object* v_infoState_944_; lean_object* v_snapshotTasks_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_959_; 
v___f_935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_935_, 0, v_a_931_);
v___x_936_ = lean_st_ref_take(v_a_919_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
v_nextMacroScope_938_ = lean_ctor_get(v___x_936_, 1);
v_ngen_939_ = lean_ctor_get(v___x_936_, 2);
v_auxDeclNGen_940_ = lean_ctor_get(v___x_936_, 3);
v_traceState_941_ = lean_ctor_get(v___x_936_, 4);
v_recordedDeps_942_ = lean_ctor_get(v___x_936_, 6);
v_messages_943_ = lean_ctor_get(v___x_936_, 7);
v_infoState_944_ = lean_ctor_get(v___x_936_, 8);
v_snapshotTasks_945_ = lean_ctor_get(v___x_936_, 9);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v___x_936_, 5);
lean_dec(v_unused_960_);
v___x_947_ = v___x_936_;
v_isShared_948_ = v_isSharedCheck_959_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snapshotTasks_945_);
lean_inc(v_infoState_944_);
lean_inc(v_messages_943_);
lean_inc(v_recordedDeps_942_);
lean_inc(v_traceState_941_);
lean_inc(v_auxDeclNGen_940_);
lean_inc(v_ngen_939_);
lean_inc(v_nextMacroScope_938_);
lean_inc(v_env_937_);
lean_dec(v___x_936_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_959_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_916_, v_env_937_, v___f_935_);
v___x_951_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 5, v___x_951_);
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_nextMacroScope_938_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_ngen_939_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_auxDeclNGen_940_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_traceState_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 5, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 6, v_recordedDeps_942_);
lean_ctor_set(v_reuseFailAlloc_958_, 7, v_messages_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 8, v_infoState_944_);
lean_ctor_set(v_reuseFailAlloc_958_, 9, v_snapshotTasks_945_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_st_ref_put(v_a_919_, v___x_953_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_949_);
v___x_956_ = v___x_933_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_949_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v_ext_916_);
v_a_962_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_930_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_930_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_970_, lean_object* v_declName_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_970_, v_declName_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_976_, lean_object* v_s_977_){
_start:
{
lean_object* v_extThms_978_; lean_object* v_funCC_979_; lean_object* v_ematch_980_; lean_object* v_inj_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_extThms_978_ = lean_ctor_get(v_s_977_, 1);
v_funCC_979_ = lean_ctor_get(v_s_977_, 2);
v_ematch_980_ = lean_ctor_get(v_s_977_, 3);
v_inj_981_ = lean_ctor_get(v_s_977_, 4);
v_isSharedCheck_988_ = !lean_is_exclusive(v_s_977_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_s_977_, 0);
lean_dec(v_unused_989_);
v___x_983_ = v_s_977_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_inj_981_);
lean_inc(v_ematch_980_);
lean_inc(v_funCC_979_);
lean_inc(v_extThms_978_);
lean_dec(v_s_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v_a_976_);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_extThms_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_funCC_979_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_ematch_980_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_inj_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_990_, lean_object* v_declName_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_991_);
v___x_996_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; lean_object* v_ext_998_; lean_object* v_toEnvExtension_999_; lean_object* v_env_1000_; lean_object* v_asyncMode_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v_casesTypes_1004_; lean_object* v___x_1005_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_997_ = lean_st_ref_get(v_a_993_);
v_ext_998_ = lean_ctor_get(v_ext_990_, 1);
v_toEnvExtension_999_ = lean_ctor_get(v_ext_998_, 0);
v_env_1000_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_env_1000_);
lean_dec(v___x_997_);
v_asyncMode_1001_ = lean_ctor_get(v_toEnvExtension_999_, 2);
v___x_1002_ = 0;
v___x_1003_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_995_, v_ext_990_, v_env_1000_, v_asyncMode_1001_, v___x_1002_);
v_casesTypes_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_casesTypes_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_1004_, v_declName_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1036_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v_nextMacroScope_1013_; lean_object* v_ngen_1014_; lean_object* v_auxDeclNGen_1015_; lean_object* v_traceState_1016_; lean_object* v_recordedDeps_1017_; lean_object* v_messages_1018_; lean_object* v_infoState_1019_; lean_object* v_snapshotTasks_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1034_; 
v___f_1010_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1010_, 0, v_a_1006_);
v___x_1011_ = lean_st_ref_take(v_a_993_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
v_nextMacroScope_1013_ = lean_ctor_get(v___x_1011_, 1);
v_ngen_1014_ = lean_ctor_get(v___x_1011_, 2);
v_auxDeclNGen_1015_ = lean_ctor_get(v___x_1011_, 3);
v_traceState_1016_ = lean_ctor_get(v___x_1011_, 4);
v_recordedDeps_1017_ = lean_ctor_get(v___x_1011_, 6);
v_messages_1018_ = lean_ctor_get(v___x_1011_, 7);
v_infoState_1019_ = lean_ctor_get(v___x_1011_, 8);
v_snapshotTasks_1020_ = lean_ctor_get(v___x_1011_, 9);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_1011_, 5);
lean_dec(v_unused_1035_);
v___x_1022_ = v___x_1011_;
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_snapshotTasks_1020_);
lean_inc(v_infoState_1019_);
lean_inc(v_messages_1018_);
lean_inc(v_recordedDeps_1017_);
lean_inc(v_traceState_1016_);
lean_inc(v_auxDeclNGen_1015_);
lean_inc(v_ngen_1014_);
lean_inc(v_nextMacroScope_1013_);
lean_inc(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_990_, v_env_1012_, v___f_1010_);
v___x_1026_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 5, v___x_1026_);
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_nextMacroScope_1013_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_ngen_1014_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_auxDeclNGen_1015_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_traceState_1016_);
lean_ctor_set(v_reuseFailAlloc_1033_, 5, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1033_, 6, v_recordedDeps_1017_);
lean_ctor_set(v_reuseFailAlloc_1033_, 7, v_messages_1018_);
lean_ctor_set(v_reuseFailAlloc_1033_, 8, v_infoState_1019_);
lean_ctor_set(v_reuseFailAlloc_1033_, 9, v_snapshotTasks_1020_);
v___x_1028_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_st_ref_put(v_a_993_, v___x_1028_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1024_);
v___x_1031_ = v___x_1008_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1024_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_ext_990_);
v_a_1037_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1005_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1005_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_dec(v_declName_991_);
lean_dec_ref(v_ext_990_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1045_, lean_object* v_declName_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1045_, v_declName_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1051_, lean_object* v_s_1052_){
_start:
{
lean_object* v_casesTypes_1053_; lean_object* v_extThms_1054_; lean_object* v_ematch_1055_; lean_object* v_inj_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_casesTypes_1053_ = lean_ctor_get(v_s_1052_, 0);
v_extThms_1054_ = lean_ctor_get(v_s_1052_, 1);
v_ematch_1055_ = lean_ctor_get(v_s_1052_, 3);
v_inj_1056_ = lean_ctor_get(v_s_1052_, 4);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_s_1052_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_s_1052_, 2);
lean_dec(v_unused_1064_);
v___x_1058_ = v_s_1052_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_inj_1056_);
lean_inc(v_ematch_1055_);
lean_inc(v_extThms_1054_);
lean_inc(v_casesTypes_1053_);
lean_dec(v_s_1052_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 2, v___x_1051_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_casesTypes_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_extThms_1054_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_ematch_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_inj_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1065_, lean_object* v_t_1066_){
_start:
{
if (lean_obj_tag(v_t_1066_) == 0)
{
lean_object* v_k_1067_; lean_object* v_v_1068_; lean_object* v_l_1069_; lean_object* v_r_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1724_; 
v_k_1067_ = lean_ctor_get(v_t_1066_, 1);
v_v_1068_ = lean_ctor_get(v_t_1066_, 2);
v_l_1069_ = lean_ctor_get(v_t_1066_, 3);
v_r_1070_ = lean_ctor_get(v_t_1066_, 4);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_t_1066_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_t_1066_, 0);
lean_dec(v_unused_1725_);
v___x_1072_ = v_t_1066_;
v_isShared_1073_ = v_isSharedCheck_1724_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_r_1070_);
lean_inc(v_l_1069_);
lean_inc(v_v_1068_);
lean_inc(v_k_1067_);
lean_dec(v_t_1066_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1724_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
uint8_t v___x_1074_; 
v___x_1074_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1065_, v_k_1067_);
switch(v___x_1074_)
{
case 0:
{
lean_object* v_impl_1075_; lean_object* v___x_1076_; 
v_impl_1075_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1065_, v_l_1069_);
v___x_1076_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1075_) == 0)
{
if (lean_obj_tag(v_r_1070_) == 0)
{
lean_object* v_size_1077_; lean_object* v_size_1078_; lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v_l_1081_; lean_object* v_r_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_size_1077_ = lean_ctor_get(v_impl_1075_, 0);
v_size_1078_ = lean_ctor_get(v_r_1070_, 0);
v_k_1079_ = lean_ctor_get(v_r_1070_, 1);
v_v_1080_ = lean_ctor_get(v_r_1070_, 2);
v_l_1081_ = lean_ctor_get(v_r_1070_, 3);
lean_inc(v_l_1081_);
v_r_1082_ = lean_ctor_get(v_r_1070_, 4);
v___x_1083_ = lean_unsigned_to_nat(3u);
v___x_1084_ = lean_nat_mul(v___x_1083_, v_size_1077_);
v___x_1085_ = lean_nat_dec_lt(v___x_1084_, v_size_1078_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_l_1081_);
v___x_1086_ = lean_nat_add(v___x_1076_, v_size_1077_);
v___x_1087_ = lean_nat_add(v___x_1086_, v_size_1078_);
lean_dec(v___x_1086_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 3, v_impl_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1087_);
v___x_1089_ = v___x_1072_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_r_1070_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_r_1082_);
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
lean_inc(v_size_1078_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1155_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_r_1070_, 2);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_1070_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1159_);
v___x_1092_ = v_r_1070_;
v_isShared_1093_ = v_isSharedCheck_1154_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_r_1070_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1154_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v_l_1097_; lean_object* v_r_1098_; lean_object* v_size_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_size_1094_ = lean_ctor_get(v_l_1081_, 0);
v_k_1095_ = lean_ctor_get(v_l_1081_, 1);
v_v_1096_ = lean_ctor_get(v_l_1081_, 2);
v_l_1097_ = lean_ctor_get(v_l_1081_, 3);
v_r_1098_ = lean_ctor_get(v_l_1081_, 4);
v_size_1099_ = lean_ctor_get(v_r_1082_, 0);
v___x_1100_ = lean_unsigned_to_nat(2u);
v___x_1101_ = lean_nat_mul(v___x_1100_, v_size_1099_);
v___x_1102_ = lean_nat_dec_lt(v_size_1094_, v___x_1101_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1130_; 
lean_inc(v_r_1098_);
lean_inc(v_l_1097_);
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_l_1081_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; lean_object* v_unused_1132_; lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; 
v_unused_1131_ = lean_ctor_get(v_l_1081_, 4);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_l_1081_, 3);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_l_1081_, 2);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_l_1081_, 1);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_l_1081_, 0);
lean_dec(v_unused_1135_);
v___x_1104_ = v_l_1081_;
v_isShared_1105_ = v_isSharedCheck_1130_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_l_1081_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1130_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1120_; 
v___x_1106_ = lean_nat_add(v___x_1076_, v_size_1077_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_size_1078_);
lean_dec(v_size_1078_);
if (lean_obj_tag(v_l_1097_) == 0)
{
lean_object* v_size_1128_; 
v_size_1128_ = lean_ctor_get(v_l_1097_, 0);
lean_inc(v_size_1128_);
v___y_1120_ = v_size_1128_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___y_1120_ = v___x_1129_;
goto v___jp_1119_;
}
v___jp_1108_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_nat_add(v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v___y_1110_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 4, v_r_1082_);
lean_ctor_set(v___x_1104_, 3, v_r_1098_);
lean_ctor_set(v___x_1104_, 2, v_v_1080_);
lean_ctor_set(v___x_1104_, 1, v_k_1079_);
lean_ctor_set(v___x_1104_, 0, v___x_1112_);
v___x_1114_ = v___x_1104_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_r_1098_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_r_1082_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___x_1114_);
lean_ctor_set(v___x_1092_, 3, v___y_1109_);
lean_ctor_set(v___x_1092_, 2, v_v_1096_);
lean_ctor_set(v___x_1092_, 1, v_k_1095_);
lean_ctor_set(v___x_1092_, 0, v___x_1107_);
v___x_1116_ = v___x_1092_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v___y_1109_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
v___jp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = lean_nat_add(v___x_1106_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec(v___x_1106_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_1097_);
lean_ctor_set(v___x_1072_, 3, v_impl_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1121_);
v___x_1123_ = v___x_1072_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_l_1097_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_nat_add(v___x_1076_, v_size_1099_);
if (lean_obj_tag(v_r_1098_) == 0)
{
lean_object* v_size_1125_; 
v_size_1125_ = lean_ctor_get(v_r_1098_, 0);
lean_inc(v_size_1125_);
v___y_1109_ = v___x_1123_;
v___y_1110_ = v___x_1124_;
v___y_1111_ = v_size_1125_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___y_1109_ = v___x_1123_;
v___y_1110_ = v___x_1124_;
v___y_1111_ = v___x_1126_;
goto v___jp_1108_;
}
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_del_object(v___x_1072_);
v___x_1136_ = lean_nat_add(v___x_1076_, v_size_1077_);
v___x_1137_ = lean_nat_add(v___x_1136_, v_size_1078_);
lean_dec(v_size_1078_);
v___x_1138_ = lean_nat_add(v___x_1136_, v_size_1094_);
lean_dec(v___x_1136_);
lean_inc_ref(v_impl_1075_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_l_1081_);
lean_ctor_set(v___x_1092_, 3, v_impl_1075_);
lean_ctor_set(v___x_1092_, 2, v_v_1068_);
lean_ctor_set(v___x_1092_, 1, v_k_1067_);
lean_ctor_set(v___x_1092_, 0, v___x_1138_);
v___x_1140_ = v___x_1092_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_l_1081_);
v___x_1140_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v_impl_1075_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_impl_1075_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_impl_1075_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_impl_1075_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_impl_1075_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_impl_1075_, 0);
lean_dec(v_unused_1152_);
v___x_1142_ = v_impl_1075_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_impl_1075_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_r_1082_);
lean_ctor_set(v___x_1142_, 3, v___x_1140_);
lean_ctor_set(v___x_1142_, 2, v_v_1080_);
lean_ctor_set(v___x_1142_, 1, v_k_1079_);
lean_ctor_set(v___x_1142_, 0, v___x_1137_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_r_1082_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v_size_1160_ = lean_ctor_get(v_impl_1075_, 0);
v___x_1161_ = lean_nat_add(v___x_1076_, v_size_1160_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 3, v_impl_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1161_);
v___x_1163_ = v___x_1072_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_r_1070_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
if (lean_obj_tag(v_r_1070_) == 0)
{
lean_object* v_l_1165_; 
v_l_1165_ = lean_ctor_get(v_r_1070_, 3);
lean_inc(v_l_1165_);
if (lean_obj_tag(v_l_1165_) == 0)
{
lean_object* v_r_1166_; 
v_r_1166_ = lean_ctor_get(v_r_1070_, 4);
lean_inc(v_r_1166_);
if (lean_obj_tag(v_r_1166_) == 0)
{
lean_object* v_size_1167_; lean_object* v_k_1168_; lean_object* v_v_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1182_; 
v_size_1167_ = lean_ctor_get(v_r_1070_, 0);
v_k_1168_ = lean_ctor_get(v_r_1070_, 1);
v_v_1169_ = lean_ctor_get(v_r_1070_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1183_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1184_);
v___x_1171_ = v_r_1070_;
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_v_1169_);
lean_inc(v_k_1168_);
lean_inc(v_size_1167_);
lean_dec(v_r_1070_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_size_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_size_1173_ = lean_ctor_get(v_l_1165_, 0);
v___x_1174_ = lean_nat_add(v___x_1076_, v_size_1167_);
lean_dec(v_size_1167_);
v___x_1175_ = lean_nat_add(v___x_1076_, v_size_1173_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 4, v_l_1165_);
lean_ctor_set(v___x_1171_, 3, v_impl_1075_);
lean_ctor_set(v___x_1171_, 2, v_v_1068_);
lean_ctor_set(v___x_1171_, 1, v_k_1067_);
lean_ctor_set(v___x_1171_, 0, v___x_1175_);
v___x_1177_ = v___x_1171_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_impl_1075_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_l_1165_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_r_1166_);
lean_ctor_set(v___x_1072_, 3, v___x_1177_);
lean_ctor_set(v___x_1072_, 2, v_v_1169_);
lean_ctor_set(v___x_1072_, 1, v_k_1168_);
lean_ctor_set(v___x_1072_, 0, v___x_1174_);
v___x_1179_ = v___x_1072_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_1169_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_r_1166_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1209_; 
v_k_1185_ = lean_ctor_get(v_r_1070_, 1);
v_v_1186_ = lean_ctor_get(v_r_1070_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1210_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1212_);
v___x_1188_ = v_r_1070_;
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_v_1186_);
lean_inc(v_k_1185_);
lean_dec(v_r_1070_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_k_1190_; lean_object* v_v_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1205_; 
v_k_1190_ = lean_ctor_get(v_l_1165_, 1);
v_v_1191_ = lean_ctor_get(v_l_1165_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_l_1165_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; lean_object* v_unused_1207_; lean_object* v_unused_1208_; 
v_unused_1206_ = lean_ctor_get(v_l_1165_, 4);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_l_1165_, 3);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_l_1165_, 0);
lean_dec(v_unused_1208_);
v___x_1193_ = v_l_1165_;
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_v_1191_);
lean_inc(v_k_1190_);
lean_dec(v_l_1165_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(3u);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 4, v_r_1166_);
lean_ctor_set(v___x_1193_, 3, v_r_1166_);
lean_ctor_set(v___x_1193_, 2, v_v_1068_);
lean_ctor_set(v___x_1193_, 1, v_k_1067_);
lean_ctor_set(v___x_1193_, 0, v___x_1076_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_r_1166_);
v___x_1197_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 3, v_r_1166_);
lean_ctor_set(v___x_1188_, 0, v___x_1076_);
v___x_1199_ = v___x_1188_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1185_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1186_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_r_1166_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1199_);
lean_ctor_set(v___x_1072_, 3, v___x_1197_);
lean_ctor_set(v___x_1072_, 2, v_v_1191_);
lean_ctor_set(v___x_1072_, 1, v_k_1190_);
lean_ctor_set(v___x_1072_, 0, v___x_1195_);
v___x_1201_ = v___x_1072_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1191_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1213_; 
v_r_1213_ = lean_ctor_get(v_r_1070_, 4);
lean_inc(v_r_1213_);
if (lean_obj_tag(v_r_1213_) == 0)
{
lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1226_; 
v_k_1214_ = lean_ctor_get(v_r_1070_, 1);
v_v_1215_ = lean_ctor_get(v_r_1070_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1227_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1229_);
v___x_1217_ = v_r_1070_;
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_dec(v_r_1070_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1226_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(3u);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 4, v_l_1165_);
lean_ctor_set(v___x_1217_, 2, v_v_1068_);
lean_ctor_set(v___x_1217_, 1, v_k_1067_);
lean_ctor_set(v___x_1217_, 0, v___x_1076_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_l_1165_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_l_1165_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_r_1213_);
lean_ctor_set(v___x_1072_, 3, v___x_1221_);
lean_ctor_set(v___x_1072_, 2, v_v_1215_);
lean_ctor_set(v___x_1072_, 1, v_k_1214_);
lean_ctor_set(v___x_1072_, 0, v___x_1219_);
v___x_1223_ = v___x_1072_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_r_1213_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_size_1230_; lean_object* v_k_1231_; lean_object* v_v_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v_size_1230_ = lean_ctor_get(v_r_1070_, 0);
v_k_1231_ = lean_ctor_get(v_r_1070_, 1);
v_v_1232_ = lean_ctor_get(v_r_1070_, 2);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1245_);
v___x_1234_ = v_r_1070_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_v_1232_);
lean_inc(v_k_1231_);
lean_inc(v_size_1230_);
lean_dec(v_r_1070_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 3, v_r_1213_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_r_1213_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_r_1213_);
v___x_1237_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(2u);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1237_);
lean_ctor_set(v___x_1072_, 3, v_r_1213_);
lean_ctor_set(v___x_1072_, 0, v___x_1238_);
v___x_1240_ = v___x_1072_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1213_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v___x_1237_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
else
{
lean_object* v___x_1247_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 3, v_r_1070_);
lean_ctor_set(v___x_1072_, 0, v___x_1076_);
v___x_1247_ = v___x_1072_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_r_1070_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_1070_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1072_);
lean_dec(v_v_1068_);
lean_dec(v_k_1067_);
if (lean_obj_tag(v_l_1069_) == 0)
{
if (lean_obj_tag(v_r_1070_) == 0)
{
lean_object* v_size_1249_; lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v_l_1252_; lean_object* v_r_1253_; lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v_l_1257_; lean_object* v_r_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_size_1249_ = lean_ctor_get(v_l_1069_, 0);
v_k_1250_ = lean_ctor_get(v_l_1069_, 1);
v_v_1251_ = lean_ctor_get(v_l_1069_, 2);
v_l_1252_ = lean_ctor_get(v_l_1069_, 3);
v_r_1253_ = lean_ctor_get(v_l_1069_, 4);
lean_inc(v_r_1253_);
v_size_1254_ = lean_ctor_get(v_r_1070_, 0);
v_k_1255_ = lean_ctor_get(v_r_1070_, 1);
v_v_1256_ = lean_ctor_get(v_r_1070_, 2);
v_l_1257_ = lean_ctor_get(v_r_1070_, 3);
lean_inc(v_l_1257_);
v_r_1258_ = lean_ctor_get(v_r_1070_, 4);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_dec_lt(v_size_1249_, v_size_1254_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1396_; 
lean_inc(v_l_1252_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1397_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_l_1069_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_l_1069_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1401_);
v___x_1262_ = v_l_1069_;
v_isShared_1263_ = v_isSharedCheck_1396_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v_l_1069_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1396_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v_tree_1265_; 
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1250_, v_v_1251_, v_l_1252_, v_r_1253_);
v_tree_1265_ = lean_ctor_get(v___x_1264_, 2);
if (lean_obj_tag(v_tree_1265_) == 0)
{
lean_object* v_k_1266_; lean_object* v_v_1267_; lean_object* v_size_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
lean_inc_ref(v_tree_1265_);
v_k_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_k_1266_);
v_v_1267_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_v_1267_);
lean_dec_ref(v___x_1264_);
v_size_1268_ = lean_ctor_get(v_tree_1265_, 0);
v___x_1269_ = lean_unsigned_to_nat(3u);
v___x_1270_ = lean_nat_mul(v___x_1269_, v_size_1268_);
v___x_1271_ = lean_nat_dec_lt(v___x_1270_, v_size_1254_);
lean_dec(v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec(v_l_1257_);
v___x_1272_ = lean_nat_add(v___x_1259_, v_size_1268_);
v___x_1273_ = lean_nat_add(v___x_1272_, v_size_1254_);
lean_dec(v___x_1272_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_r_1070_);
lean_ctor_set(v___x_1262_, 3, v_tree_1265_);
lean_ctor_set(v___x_1262_, 2, v_v_1267_);
lean_ctor_set(v___x_1262_, 1, v_k_1266_);
lean_ctor_set(v___x_1262_, 0, v___x_1273_);
v___x_1275_ = v___x_1262_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1267_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_tree_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_r_1070_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1331_; 
lean_inc(v_r_1258_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
lean_inc(v_size_1254_);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; lean_object* v_unused_1333_; lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; 
v_unused_1332_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_r_1070_, 2);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_r_1070_, 1);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1336_);
v___x_1278_ = v_r_1070_;
v_isShared_1279_ = v_isSharedCheck_1331_;
goto v_resetjp_1277_;
}
else
{
lean_dec(v_r_1070_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1331_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_size_1280_; lean_object* v_k_1281_; lean_object* v_v_1282_; lean_object* v_l_1283_; lean_object* v_r_1284_; lean_object* v_size_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_size_1280_ = lean_ctor_get(v_l_1257_, 0);
v_k_1281_ = lean_ctor_get(v_l_1257_, 1);
v_v_1282_ = lean_ctor_get(v_l_1257_, 2);
v_l_1283_ = lean_ctor_get(v_l_1257_, 3);
v_r_1284_ = lean_ctor_get(v_l_1257_, 4);
v_size_1285_ = lean_ctor_get(v_r_1258_, 0);
v___x_1286_ = lean_unsigned_to_nat(2u);
v___x_1287_ = lean_nat_mul(v___x_1286_, v_size_1285_);
v___x_1288_ = lean_nat_dec_lt(v_size_1280_, v___x_1287_);
lean_dec(v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1316_; 
lean_inc(v_r_1284_);
lean_inc(v_l_1283_);
lean_inc(v_v_1282_);
lean_inc(v_k_1281_);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_l_1257_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; 
v_unused_1317_ = lean_ctor_get(v_l_1257_, 4);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_l_1257_, 3);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_l_1257_, 2);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_l_1257_, 1);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_l_1257_, 0);
lean_dec(v_unused_1321_);
v___x_1290_ = v_l_1257_;
v_isShared_1291_ = v_isSharedCheck_1316_;
goto v_resetjp_1289_;
}
else
{
lean_dec(v_l_1257_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1316_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1306_; 
v___x_1292_ = lean_nat_add(v___x_1259_, v_size_1268_);
v___x_1293_ = lean_nat_add(v___x_1292_, v_size_1254_);
lean_dec(v_size_1254_);
if (lean_obj_tag(v_l_1283_) == 0)
{
lean_object* v_size_1314_; 
v_size_1314_ = lean_ctor_get(v_l_1283_, 0);
lean_inc(v_size_1314_);
v___y_1306_ = v_size_1314_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___y_1306_ = v___x_1315_;
goto v___jp_1305_;
}
v___jp_1294_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_nat_add(v___y_1295_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec(v___y_1295_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 4, v_r_1258_);
lean_ctor_set(v___x_1290_, 3, v_r_1284_);
lean_ctor_set(v___x_1290_, 2, v_v_1256_);
lean_ctor_set(v___x_1290_, 1, v_k_1255_);
lean_ctor_set(v___x_1290_, 0, v___x_1298_);
v___x_1300_ = v___x_1290_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_r_1284_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v_r_1258_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v___x_1300_);
lean_ctor_set(v___x_1278_, 3, v___y_1296_);
lean_ctor_set(v___x_1278_, 2, v_v_1282_);
lean_ctor_set(v___x_1278_, 1, v_k_1281_);
lean_ctor_set(v___x_1278_, 0, v___x_1293_);
v___x_1302_ = v___x_1278_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1281_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1282_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v___y_1296_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_nat_add(v___x_1292_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec(v___x_1292_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_l_1283_);
lean_ctor_set(v___x_1262_, 3, v_tree_1265_);
lean_ctor_set(v___x_1262_, 2, v_v_1267_);
lean_ctor_set(v___x_1262_, 1, v_k_1266_);
lean_ctor_set(v___x_1262_, 0, v___x_1307_);
v___x_1309_ = v___x_1262_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1266_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1267_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_tree_1265_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_l_1283_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_nat_add(v___x_1259_, v_size_1285_);
if (lean_obj_tag(v_r_1284_) == 0)
{
lean_object* v_size_1311_; 
v_size_1311_ = lean_ctor_get(v_r_1284_, 0);
lean_inc(v_size_1311_);
v___y_1295_ = v___x_1310_;
v___y_1296_ = v___x_1309_;
v___y_1297_ = v_size_1311_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___y_1295_ = v___x_1310_;
v___y_1296_ = v___x_1309_;
v___y_1297_ = v___x_1312_;
goto v___jp_1294_;
}
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1322_ = lean_nat_add(v___x_1259_, v_size_1268_);
v___x_1323_ = lean_nat_add(v___x_1322_, v_size_1254_);
lean_dec(v_size_1254_);
v___x_1324_ = lean_nat_add(v___x_1322_, v_size_1280_);
lean_dec(v___x_1322_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v_l_1257_);
lean_ctor_set(v___x_1278_, 3, v_tree_1265_);
lean_ctor_set(v___x_1278_, 2, v_v_1267_);
lean_ctor_set(v___x_1278_, 1, v_k_1266_);
lean_ctor_set(v___x_1278_, 0, v___x_1324_);
v___x_1326_ = v___x_1278_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1266_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1267_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_tree_1265_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_l_1257_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_r_1258_);
lean_ctor_set(v___x_1262_, 3, v___x_1326_);
lean_ctor_set(v___x_1262_, 2, v_v_1256_);
lean_ctor_set(v___x_1262_, 1, v_k_1255_);
lean_ctor_set(v___x_1262_, 0, v___x_1323_);
v___x_1328_ = v___x_1262_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_r_1258_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
else
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1390_; 
lean_inc(v_r_1258_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
lean_inc(v_size_1254_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; lean_object* v_unused_1395_; 
v_unused_1391_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_r_1070_, 2);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_r_1070_, 1);
lean_dec(v_unused_1394_);
v_unused_1395_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1395_);
v___x_1338_ = v_r_1070_;
v_isShared_1339_ = v_isSharedCheck_1390_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v_r_1070_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1390_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
if (lean_obj_tag(v_l_1257_) == 0)
{
if (lean_obj_tag(v_r_1258_) == 0)
{
lean_object* v_k_1340_; lean_object* v_v_1341_; lean_object* v_size_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_inc(v_tree_1265_);
v_k_1340_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_k_1340_);
v_v_1341_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_v_1341_);
lean_dec_ref(v___x_1264_);
v_size_1342_ = lean_ctor_get(v_l_1257_, 0);
v___x_1343_ = lean_nat_add(v___x_1259_, v_size_1254_);
lean_dec(v_size_1254_);
v___x_1344_ = lean_nat_add(v___x_1259_, v_size_1342_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 4, v_l_1257_);
lean_ctor_set(v___x_1338_, 3, v_tree_1265_);
lean_ctor_set(v___x_1338_, 2, v_v_1341_);
lean_ctor_set(v___x_1338_, 1, v_k_1340_);
lean_ctor_set(v___x_1338_, 0, v___x_1344_);
v___x_1346_ = v___x_1338_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1340_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1341_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_tree_1265_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_l_1257_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_r_1258_);
lean_ctor_set(v___x_1262_, 3, v___x_1346_);
lean_ctor_set(v___x_1262_, 2, v_v_1256_);
lean_ctor_set(v___x_1262_, 1, v_k_1255_);
lean_ctor_set(v___x_1262_, 0, v___x_1343_);
v___x_1348_ = v___x_1262_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_r_1258_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_k_1351_; lean_object* v_v_1352_; lean_object* v_k_1353_; lean_object* v_v_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_size_1254_);
v_k_1351_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_k_1351_);
v_v_1352_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_v_1352_);
lean_dec_ref(v___x_1264_);
v_k_1353_ = lean_ctor_get(v_l_1257_, 1);
v_v_1354_ = lean_ctor_get(v_l_1257_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_l_1257_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1369_ = lean_ctor_get(v_l_1257_, 4);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_l_1257_, 3);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_l_1257_, 0);
lean_dec(v_unused_1371_);
v___x_1356_ = v_l_1257_;
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_v_1354_);
lean_inc(v_k_1353_);
lean_dec(v_l_1257_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(3u);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 4, v_r_1258_);
lean_ctor_set(v___x_1356_, 3, v_r_1258_);
lean_ctor_set(v___x_1356_, 2, v_v_1352_);
lean_ctor_set(v___x_1356_, 1, v_k_1351_);
lean_ctor_set(v___x_1356_, 0, v___x_1259_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1351_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1352_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_r_1258_);
v___x_1360_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 3, v_r_1258_);
lean_ctor_set(v___x_1338_, 0, v___x_1259_);
v___x_1362_ = v___x_1338_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1258_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v___x_1362_);
lean_ctor_set(v___x_1262_, 3, v___x_1360_);
lean_ctor_set(v___x_1262_, 2, v_v_1354_);
lean_ctor_set(v___x_1262_, 1, v_k_1353_);
lean_ctor_set(v___x_1262_, 0, v___x_1358_);
v___x_1364_ = v___x_1262_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1258_) == 0)
{
lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec(v_size_1254_);
v_k_1372_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_k_1372_);
v_v_1373_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_v_1373_);
lean_dec_ref(v___x_1264_);
v___x_1374_ = lean_unsigned_to_nat(3u);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 4, v_l_1257_);
lean_ctor_set(v___x_1338_, 2, v_v_1373_);
lean_ctor_set(v___x_1338_, 1, v_k_1372_);
lean_ctor_set(v___x_1338_, 0, v___x_1259_);
v___x_1376_ = v___x_1338_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_l_1257_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_l_1257_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v_r_1258_);
lean_ctor_set(v___x_1262_, 3, v___x_1376_);
lean_ctor_set(v___x_1262_, 2, v_v_1256_);
lean_ctor_set(v___x_1262_, 1, v_k_1255_);
lean_ctor_set(v___x_1262_, 0, v___x_1374_);
v___x_1378_ = v___x_1262_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_r_1258_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v___x_1384_; 
v_k_1381_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_k_1381_);
v_v_1382_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_v_1382_);
lean_dec_ref(v___x_1264_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 3, v_r_1258_);
v___x_1384_ = v___x_1338_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_size_1254_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1255_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1256_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_r_1258_);
v___x_1384_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_unsigned_to_nat(2u);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 4, v___x_1384_);
lean_ctor_set(v___x_1262_, 3, v_r_1258_);
lean_ctor_set(v___x_1262_, 2, v_v_1382_);
lean_ctor_set(v___x_1262_, 1, v_k_1381_);
lean_ctor_set(v___x_1262_, 0, v___x_1385_);
v___x_1387_ = v___x_1262_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_r_1258_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___x_1384_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
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
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1554_; 
lean_inc(v_r_1258_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_r_1070_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1555_ = lean_ctor_get(v_r_1070_, 4);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_r_1070_, 3);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_r_1070_, 2);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_r_1070_, 1);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_r_1070_, 0);
lean_dec(v_unused_1559_);
v___x_1403_ = v_r_1070_;
v_isShared_1404_ = v_isSharedCheck_1554_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_r_1070_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1554_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v_tree_1406_; 
v___x_1405_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1255_, v_v_1256_, v_l_1257_, v_r_1258_);
v_tree_1406_ = lean_ctor_get(v___x_1405_, 2);
lean_inc(v_tree_1406_);
if (lean_obj_tag(v_tree_1406_) == 0)
{
lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v_size_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_k_1407_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_k_1407_);
v_v_1408_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_v_1408_);
lean_dec_ref(v___x_1405_);
v_size_1409_ = lean_ctor_get(v_tree_1406_, 0);
v___x_1410_ = lean_unsigned_to_nat(3u);
v___x_1411_ = lean_nat_mul(v___x_1410_, v_size_1409_);
v___x_1412_ = lean_nat_dec_lt(v___x_1411_, v_size_1249_);
lean_dec(v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_dec(v_r_1253_);
v___x_1413_ = lean_nat_add(v___x_1259_, v_size_1249_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1409_);
lean_dec(v___x_1413_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_tree_1406_);
lean_ctor_set(v___x_1403_, 3, v_l_1069_);
lean_ctor_set(v___x_1403_, 2, v_v_1408_);
lean_ctor_set(v___x_1403_, 1, v_k_1407_);
lean_ctor_set(v___x_1403_, 0, v___x_1414_);
v___x_1416_ = v___x_1403_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_tree_1406_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_l_1252_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_inc(v_size_1249_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1484_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_l_1069_, 2);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1069_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1488_);
v___x_1419_ = v_l_1069_;
v_isShared_1420_ = v_isSharedCheck_1483_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v_l_1069_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1483_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_size_1421_; lean_object* v_size_1422_; lean_object* v_k_1423_; lean_object* v_v_1424_; lean_object* v_l_1425_; lean_object* v_r_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_size_1421_ = lean_ctor_get(v_l_1252_, 0);
v_size_1422_ = lean_ctor_get(v_r_1253_, 0);
v_k_1423_ = lean_ctor_get(v_r_1253_, 1);
v_v_1424_ = lean_ctor_get(v_r_1253_, 2);
v_l_1425_ = lean_ctor_get(v_r_1253_, 3);
v_r_1426_ = lean_ctor_get(v_r_1253_, 4);
v___x_1427_ = lean_unsigned_to_nat(2u);
v___x_1428_ = lean_nat_mul(v___x_1427_, v_size_1421_);
v___x_1429_ = lean_nat_dec_lt(v_size_1422_, v___x_1428_);
lean_dec(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1467_; 
lean_inc(v_r_1426_);
lean_inc(v_l_1425_);
lean_inc(v_v_1424_);
lean_inc(v_k_1423_);
lean_del_object(v___x_1419_);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_r_1253_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1468_ = lean_ctor_get(v_r_1253_, 4);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1253_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_r_1253_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_r_1253_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1253_, 0);
lean_dec(v_unused_1472_);
v___x_1431_ = v_r_1253_;
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_r_1253_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1467_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___x_1455_; lean_object* v___y_1457_; 
v___x_1433_ = lean_nat_add(v___x_1259_, v_size_1249_);
lean_dec(v_size_1249_);
v___x_1434_ = lean_nat_add(v___x_1433_, v_size_1409_);
lean_dec(v___x_1433_);
v___x_1455_ = lean_nat_add(v___x_1259_, v_size_1421_);
if (lean_obj_tag(v_l_1425_) == 0)
{
lean_object* v_size_1465_; 
v_size_1465_ = lean_ctor_get(v_l_1425_, 0);
lean_inc(v_size_1465_);
v___y_1457_ = v_size_1465_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___y_1457_ = v___x_1466_;
goto v___jp_1456_;
}
v___jp_1435_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_nat_add(v___y_1436_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec(v___y_1436_);
lean_inc_ref(v_tree_1406_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 4, v_tree_1406_);
lean_ctor_set(v___x_1431_, 3, v_r_1426_);
lean_ctor_set(v___x_1431_, 2, v_v_1408_);
lean_ctor_set(v___x_1431_, 1, v_k_1407_);
lean_ctor_set(v___x_1431_, 0, v___x_1439_);
v___x_1441_ = v___x_1431_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_r_1426_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_tree_1406_);
v___x_1441_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v_tree_1406_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; 
v_unused_1449_ = lean_ctor_get(v_tree_1406_, 4);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_tree_1406_, 3);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_tree_1406_, 2);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_tree_1406_, 1);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_tree_1406_, 0);
lean_dec(v_unused_1453_);
v___x_1443_ = v_tree_1406_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_tree_1406_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1441_);
lean_ctor_set(v___x_1443_, 3, v___y_1437_);
lean_ctor_set(v___x_1443_, 2, v_v_1424_);
lean_ctor_set(v___x_1443_, 1, v_k_1423_);
lean_ctor_set(v___x_1443_, 0, v___x_1434_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_k_1423_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_v_1424_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v___y_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v___x_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_nat_add(v___x_1455_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec(v___x_1455_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_l_1425_);
lean_ctor_set(v___x_1403_, 3, v_l_1252_);
lean_ctor_set(v___x_1403_, 2, v_v_1251_);
lean_ctor_set(v___x_1403_, 1, v_k_1250_);
lean_ctor_set(v___x_1403_, 0, v___x_1458_);
v___x_1460_ = v___x_1403_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_l_1425_);
v___x_1460_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_nat_add(v___x_1259_, v_size_1409_);
if (lean_obj_tag(v_r_1426_) == 0)
{
lean_object* v_size_1462_; 
v_size_1462_ = lean_ctor_get(v_r_1426_, 0);
lean_inc(v_size_1462_);
v___y_1436_ = v___x_1461_;
v___y_1437_ = v___x_1460_;
v___y_1438_ = v_size_1462_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___y_1436_ = v___x_1461_;
v___y_1437_ = v___x_1460_;
v___y_1438_ = v___x_1463_;
goto v___jp_1435_;
}
}
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1473_ = lean_nat_add(v___x_1259_, v_size_1249_);
lean_dec(v_size_1249_);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1409_);
lean_dec(v___x_1473_);
v___x_1475_ = lean_nat_add(v___x_1259_, v_size_1409_);
v___x_1476_ = lean_nat_add(v___x_1475_, v_size_1422_);
lean_dec(v___x_1475_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_tree_1406_);
lean_ctor_set(v___x_1403_, 3, v_r_1253_);
lean_ctor_set(v___x_1403_, 2, v_v_1408_);
lean_ctor_set(v___x_1403_, 1, v_k_1407_);
lean_ctor_set(v___x_1403_, 0, v___x_1476_);
v___x_1478_ = v___x_1403_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1253_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_tree_1406_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v___x_1478_);
lean_ctor_set(v___x_1419_, 0, v___x_1474_);
v___x_1480_ = v___x_1419_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1252_) == 0)
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1512_; 
lean_inc_ref(v_l_1252_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_inc(v_size_1249_);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; 
v_unused_1513_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_l_1069_, 2);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_l_1069_, 1);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1517_);
v___x_1490_ = v_l_1069_;
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v_l_1069_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1512_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
if (lean_obj_tag(v_r_1253_) == 0)
{
lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v_size_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v_k_1492_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_k_1492_);
v_v_1493_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_v_1493_);
lean_dec_ref(v___x_1405_);
v_size_1494_ = lean_ctor_get(v_r_1253_, 0);
v___x_1495_ = lean_nat_add(v___x_1259_, v_size_1249_);
lean_dec(v_size_1249_);
v___x_1496_ = lean_nat_add(v___x_1259_, v_size_1494_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_tree_1406_);
lean_ctor_set(v___x_1403_, 3, v_r_1253_);
lean_ctor_set(v___x_1403_, 2, v_v_1493_);
lean_ctor_set(v___x_1403_, 1, v_k_1492_);
lean_ctor_set(v___x_1403_, 0, v___x_1496_);
v___x_1498_ = v___x_1403_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1493_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_r_1253_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_tree_1406_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v___x_1498_);
lean_ctor_set(v___x_1490_, 0, v___x_1495_);
v___x_1500_ = v___x_1490_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_k_1503_; lean_object* v_v_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_dec(v_size_1249_);
v_k_1503_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_k_1503_);
v_v_1504_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_v_1504_);
lean_dec_ref(v___x_1405_);
v___x_1505_ = lean_unsigned_to_nat(3u);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_r_1253_);
lean_ctor_set(v___x_1403_, 3, v_r_1253_);
lean_ctor_set(v___x_1403_, 2, v_v_1504_);
lean_ctor_set(v___x_1403_, 1, v_k_1503_);
lean_ctor_set(v___x_1403_, 0, v___x_1259_);
v___x_1507_ = v___x_1403_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1503_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1504_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_r_1253_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_r_1253_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v___x_1507_);
lean_ctor_set(v___x_1490_, 0, v___x_1505_);
v___x_1509_ = v___x_1490_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1253_) == 0)
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1542_; 
lean_inc(v_l_1252_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1543_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1069_, 2);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_l_1069_, 1);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1547_);
v___x_1519_ = v_l_1069_;
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_l_1069_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_k_1523_; lean_object* v_v_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1538_; 
v_k_1521_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_v_1522_);
lean_dec_ref(v___x_1405_);
v_k_1523_ = lean_ctor_get(v_r_1253_, 1);
v_v_1524_ = lean_ctor_get(v_r_1253_, 2);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_r_1253_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1539_ = lean_ctor_get(v_r_1253_, 4);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_r_1253_, 3);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_r_1253_, 0);
lean_dec(v_unused_1541_);
v___x_1526_ = v_r_1253_;
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_v_1524_);
lean_inc(v_k_1523_);
lean_dec(v_r_1253_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_unsigned_to_nat(3u);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 4, v_l_1252_);
lean_ctor_set(v___x_1526_, 3, v_l_1252_);
lean_ctor_set(v___x_1526_, 2, v_v_1251_);
lean_ctor_set(v___x_1526_, 1, v_k_1250_);
lean_ctor_set(v___x_1526_, 0, v___x_1259_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_l_1252_);
v___x_1530_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_l_1252_);
lean_ctor_set(v___x_1403_, 3, v_l_1252_);
lean_ctor_set(v___x_1403_, 2, v_v_1522_);
lean_ctor_set(v___x_1403_, 1, v_k_1521_);
lean_ctor_set(v___x_1403_, 0, v___x_1259_);
v___x_1532_ = v___x_1403_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_l_1252_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_l_1252_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 4, v___x_1532_);
lean_ctor_set(v___x_1519_, 3, v___x_1530_);
lean_ctor_set(v___x_1519_, 2, v_v_1524_);
lean_ctor_set(v___x_1519_, 1, v_k_1523_);
lean_ctor_set(v___x_1519_, 0, v___x_1528_);
v___x_1534_ = v___x_1519_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_k_1523_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_v_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
}
else
{
lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v_k_1548_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_k_1548_);
v_v_1549_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_v_1549_);
lean_dec_ref(v___x_1405_);
v___x_1550_ = lean_unsigned_to_nat(2u);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_r_1253_);
lean_ctor_set(v___x_1403_, 3, v_l_1069_);
lean_ctor_set(v___x_1403_, 2, v_v_1549_);
lean_ctor_set(v___x_1403_, 1, v_k_1548_);
lean_ctor_set(v___x_1403_, 0, v___x_1550_);
v___x_1552_ = v___x_1403_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1548_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1549_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1253_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
}
else
{
return v_l_1069_;
}
}
else
{
return v_r_1070_;
}
}
default: 
{
lean_object* v_impl_1560_; lean_object* v___x_1561_; 
v_impl_1560_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1065_, v_r_1070_);
v___x_1561_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1560_) == 0)
{
if (lean_obj_tag(v_l_1069_) == 0)
{
lean_object* v_size_1562_; lean_object* v_size_1563_; lean_object* v_k_1564_; lean_object* v_v_1565_; lean_object* v_l_1566_; lean_object* v_r_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_size_1562_ = lean_ctor_get(v_impl_1560_, 0);
v_size_1563_ = lean_ctor_get(v_l_1069_, 0);
v_k_1564_ = lean_ctor_get(v_l_1069_, 1);
v_v_1565_ = lean_ctor_get(v_l_1069_, 2);
v_l_1566_ = lean_ctor_get(v_l_1069_, 3);
v_r_1567_ = lean_ctor_get(v_l_1069_, 4);
lean_inc(v_r_1567_);
v___x_1568_ = lean_unsigned_to_nat(3u);
v___x_1569_ = lean_nat_mul(v___x_1568_, v_size_1562_);
v___x_1570_ = lean_nat_dec_lt(v___x_1569_, v_size_1563_);
lean_dec(v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
lean_dec(v_r_1567_);
v___x_1571_ = lean_nat_add(v___x_1561_, v_size_1563_);
v___x_1572_ = lean_nat_add(v___x_1571_, v_size_1562_);
lean_dec(v___x_1571_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_impl_1560_);
lean_ctor_set(v___x_1072_, 0, v___x_1572_);
v___x_1574_ = v___x_1072_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_impl_1560_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1641_; 
lean_inc(v_l_1566_);
lean_inc(v_v_1565_);
lean_inc(v_k_1564_);
lean_inc(v_size_1563_);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; lean_object* v_unused_1646_; 
v_unused_1642_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_l_1069_, 2);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_l_1069_, 1);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1646_);
v___x_1577_ = v_l_1069_;
v_isShared_1578_ = v_isSharedCheck_1641_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v_l_1069_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1641_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_size_1579_; lean_object* v_size_1580_; lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_l_1583_; lean_object* v_r_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_size_1579_ = lean_ctor_get(v_l_1566_, 0);
v_size_1580_ = lean_ctor_get(v_r_1567_, 0);
v_k_1581_ = lean_ctor_get(v_r_1567_, 1);
v_v_1582_ = lean_ctor_get(v_r_1567_, 2);
v_l_1583_ = lean_ctor_get(v_r_1567_, 3);
v_r_1584_ = lean_ctor_get(v_r_1567_, 4);
v___x_1585_ = lean_unsigned_to_nat(2u);
v___x_1586_ = lean_nat_mul(v___x_1585_, v_size_1579_);
v___x_1587_ = lean_nat_dec_lt(v_size_1580_, v___x_1586_);
lean_dec(v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1616_; 
lean_inc(v_r_1584_);
lean_inc(v_l_1583_);
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_r_1567_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; 
v_unused_1617_ = lean_ctor_get(v_r_1567_, 4);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_r_1567_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_r_1567_, 2);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_r_1567_, 1);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_r_1567_, 0);
lean_dec(v_unused_1621_);
v___x_1589_ = v_r_1567_;
v_isShared_1590_ = v_isSharedCheck_1616_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v_r_1567_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1616_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___x_1604_; lean_object* v___y_1606_; 
v___x_1591_ = lean_nat_add(v___x_1561_, v_size_1563_);
lean_dec(v_size_1563_);
v___x_1592_ = lean_nat_add(v___x_1591_, v_size_1562_);
lean_dec(v___x_1591_);
v___x_1604_ = lean_nat_add(v___x_1561_, v_size_1579_);
if (lean_obj_tag(v_l_1583_) == 0)
{
lean_object* v_size_1614_; 
v_size_1614_ = lean_ctor_get(v_l_1583_, 0);
lean_inc(v_size_1614_);
v___y_1606_ = v_size_1614_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___y_1606_ = v___x_1615_;
goto v___jp_1605_;
}
v___jp_1593_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_nat_add(v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v_impl_1560_);
lean_ctor_set(v___x_1589_, 3, v_r_1584_);
lean_ctor_set(v___x_1589_, 2, v_v_1068_);
lean_ctor_set(v___x_1589_, 1, v_k_1067_);
lean_ctor_set(v___x_1589_, 0, v___x_1597_);
v___x_1599_ = v___x_1589_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_r_1584_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_impl_1560_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v___x_1599_);
lean_ctor_set(v___x_1577_, 3, v___y_1594_);
lean_ctor_set(v___x_1577_, 2, v_v_1582_);
lean_ctor_set(v___x_1577_, 1, v_k_1581_);
lean_ctor_set(v___x_1577_, 0, v___x_1592_);
v___x_1601_ = v___x_1577_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v___y_1594_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_nat_add(v___x_1604_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec(v___x_1604_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_1583_);
lean_ctor_set(v___x_1072_, 3, v_l_1566_);
lean_ctor_set(v___x_1072_, 2, v_v_1565_);
lean_ctor_set(v___x_1072_, 1, v_k_1564_);
lean_ctor_set(v___x_1072_, 0, v___x_1607_);
v___x_1609_ = v___x_1072_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1564_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1565_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_l_1566_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_l_1583_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_nat_add(v___x_1561_, v_size_1562_);
if (lean_obj_tag(v_r_1584_) == 0)
{
lean_object* v_size_1611_; 
v_size_1611_ = lean_ctor_get(v_r_1584_, 0);
lean_inc(v_size_1611_);
v___y_1594_ = v___x_1609_;
v___y_1595_ = v___x_1610_;
v___y_1596_ = v_size_1611_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___y_1594_ = v___x_1609_;
v___y_1595_ = v___x_1610_;
v___y_1596_ = v___x_1612_;
goto v___jp_1593_;
}
}
}
}
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_del_object(v___x_1072_);
v___x_1622_ = lean_nat_add(v___x_1561_, v_size_1563_);
lean_dec(v_size_1563_);
v___x_1623_ = lean_nat_add(v___x_1622_, v_size_1562_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_nat_add(v___x_1561_, v_size_1562_);
v___x_1625_ = lean_nat_add(v___x_1624_, v_size_1580_);
lean_dec(v___x_1624_);
lean_inc_ref(v_impl_1560_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v_impl_1560_);
lean_ctor_set(v___x_1577_, 3, v_r_1567_);
lean_ctor_set(v___x_1577_, 2, v_v_1068_);
lean_ctor_set(v___x_1577_, 1, v_k_1067_);
lean_ctor_set(v___x_1577_, 0, v___x_1625_);
v___x_1627_ = v___x_1577_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_r_1567_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_impl_1560_);
v___x_1627_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_isSharedCheck_1634_ = !lean_is_exclusive(v_impl_1560_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; 
v_unused_1635_ = lean_ctor_get(v_impl_1560_, 4);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_impl_1560_, 3);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_impl_1560_, 2);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_impl_1560_, 1);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_impl_1560_, 0);
lean_dec(v_unused_1639_);
v___x_1629_ = v_impl_1560_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v_impl_1560_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 4, v___x_1627_);
lean_ctor_set(v___x_1629_, 3, v_l_1566_);
lean_ctor_set(v___x_1629_, 2, v_v_1565_);
lean_ctor_set(v___x_1629_, 1, v_k_1564_);
lean_ctor_set(v___x_1629_, 0, v___x_1623_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_k_1564_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_v_1565_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_l_1566_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v___x_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v_size_1647_ = lean_ctor_get(v_impl_1560_, 0);
v___x_1648_ = lean_nat_add(v___x_1561_, v_size_1647_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_impl_1560_);
lean_ctor_set(v___x_1072_, 0, v___x_1648_);
v___x_1650_ = v___x_1072_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_impl_1560_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
if (lean_obj_tag(v_l_1069_) == 0)
{
lean_object* v_l_1652_; 
v_l_1652_ = lean_ctor_get(v_l_1069_, 3);
if (lean_obj_tag(v_l_1652_) == 0)
{
lean_object* v_r_1653_; 
lean_inc_ref(v_l_1652_);
v_r_1653_ = lean_ctor_get(v_l_1069_, 4);
lean_inc(v_r_1653_);
if (lean_obj_tag(v_r_1653_) == 0)
{
lean_object* v_size_1654_; lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1669_; 
v_size_1654_ = lean_ctor_get(v_l_1069_, 0);
v_k_1655_ = lean_ctor_get(v_l_1069_, 1);
v_v_1656_ = lean_ctor_get(v_l_1069_, 2);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; lean_object* v_unused_1671_; 
v_unused_1670_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1671_);
v___x_1658_ = v_l_1069_;
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
lean_inc(v_size_1654_);
lean_dec(v_l_1069_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_size_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v_size_1660_ = lean_ctor_get(v_r_1653_, 0);
v___x_1661_ = lean_nat_add(v___x_1561_, v_size_1654_);
lean_dec(v_size_1654_);
v___x_1662_ = lean_nat_add(v___x_1561_, v_size_1660_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v_impl_1560_);
lean_ctor_set(v___x_1658_, 3, v_r_1653_);
lean_ctor_set(v___x_1658_, 2, v_v_1068_);
lean_ctor_set(v___x_1658_, 1, v_k_1067_);
lean_ctor_set(v___x_1658_, 0, v___x_1662_);
v___x_1664_ = v___x_1658_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_r_1653_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_impl_1560_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1664_);
lean_ctor_set(v___x_1072_, 3, v_l_1652_);
lean_ctor_set(v___x_1072_, 2, v_v_1656_);
lean_ctor_set(v___x_1072_, 1, v_k_1655_);
lean_ctor_set(v___x_1072_, 0, v___x_1661_);
v___x_1666_ = v___x_1072_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_l_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1684_; 
v_k_1672_ = lean_ctor_get(v_l_1069_, 1);
v_v_1673_ = lean_ctor_get(v_l_1069_, 2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1685_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1687_);
v___x_1675_ = v_l_1069_;
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_dec(v_l_1069_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(3u);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v_r_1653_);
lean_ctor_set(v___x_1675_, 2, v_v_1068_);
lean_ctor_set(v___x_1675_, 1, v_k_1067_);
lean_ctor_set(v___x_1675_, 0, v___x_1561_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_r_1653_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_r_1653_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1679_);
lean_ctor_set(v___x_1072_, 3, v_l_1652_);
lean_ctor_set(v___x_1072_, 2, v_v_1673_);
lean_ctor_set(v___x_1072_, 1, v_k_1672_);
lean_ctor_set(v___x_1072_, 0, v___x_1677_);
v___x_1681_ = v___x_1072_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_l_1652_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
else
{
lean_object* v_r_1688_; 
v_r_1688_ = lean_ctor_get(v_l_1069_, 4);
lean_inc(v_r_1688_);
if (lean_obj_tag(v_r_1688_) == 0)
{
lean_object* v_k_1689_; lean_object* v_v_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1713_; 
lean_inc(v_l_1652_);
v_k_1689_ = lean_ctor_get(v_l_1069_, 1);
v_v_1690_ = lean_ctor_get(v_l_1069_, 2);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_l_1069_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; lean_object* v_unused_1715_; lean_object* v_unused_1716_; 
v_unused_1714_ = lean_ctor_get(v_l_1069_, 4);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_l_1069_, 3);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v_l_1069_, 0);
lean_dec(v_unused_1716_);
v___x_1692_ = v_l_1069_;
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_v_1690_);
lean_inc(v_k_1689_);
lean_dec(v_l_1069_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_k_1694_; lean_object* v_v_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1709_; 
v_k_1694_ = lean_ctor_get(v_r_1688_, 1);
v_v_1695_ = lean_ctor_get(v_r_1688_, 2);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_r_1688_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1710_ = lean_ctor_get(v_r_1688_, 4);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_r_1688_, 3);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_r_1688_, 0);
lean_dec(v_unused_1712_);
v___x_1697_ = v_r_1688_;
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_v_1695_);
lean_inc(v_k_1694_);
lean_dec(v_r_1688_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1709_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_unsigned_to_nat(3u);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 4, v_l_1652_);
lean_ctor_set(v___x_1697_, 3, v_l_1652_);
lean_ctor_set(v___x_1697_, 2, v_v_1690_);
lean_ctor_set(v___x_1697_, 1, v_k_1689_);
lean_ctor_set(v___x_1697_, 0, v___x_1561_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_k_1689_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_v_1690_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_l_1652_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v_l_1652_);
v___x_1701_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 4, v_l_1652_);
lean_ctor_set(v___x_1692_, 2, v_v_1068_);
lean_ctor_set(v___x_1692_, 1, v_k_1067_);
lean_ctor_set(v___x_1692_, 0, v___x_1561_);
v___x_1703_ = v___x_1692_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1652_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_l_1652_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1703_);
lean_ctor_set(v___x_1072_, 3, v___x_1701_);
lean_ctor_set(v___x_1072_, 2, v_v_1695_);
lean_ctor_set(v___x_1072_, 1, v_k_1694_);
lean_ctor_set(v___x_1072_, 0, v___x_1699_);
v___x_1705_ = v___x_1072_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_unsigned_to_nat(2u);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_r_1688_);
lean_ctor_set(v___x_1072_, 0, v___x_1717_);
v___x_1719_ = v___x_1072_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v_r_1688_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1722_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_1069_);
lean_ctor_set(v___x_1072_, 0, v___x_1561_);
v___x_1722_ = v___x_1072_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1067_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1068_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_l_1069_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_l_1069_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
else
{
return v_t_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1726_, lean_object* v_t_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1726_, v_t_1727_);
lean_dec(v_k_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1729_, lean_object* v_declName_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_ext_1736_; lean_object* v_toEnvExtension_1737_; lean_object* v_env_1738_; lean_object* v_asyncMode_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___y_1743_; lean_object* v_funCC_1770_; uint8_t v___x_1771_; 
v___x_1734_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1735_ = lean_st_ref_get(v_a_1732_);
v_ext_1736_ = lean_ctor_get(v_ext_1729_, 1);
v_toEnvExtension_1737_ = lean_ctor_get(v_ext_1736_, 0);
v_env_1738_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_ref(v_env_1738_);
lean_dec(v___x_1735_);
v_asyncMode_1739_ = lean_ctor_get(v_toEnvExtension_1737_, 2);
v___x_1740_ = 0;
v___x_1741_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1734_, v_ext_1729_, v_env_1738_, v_asyncMode_1739_, v___x_1740_);
v_funCC_1770_ = lean_ctor_get(v___x_1741_, 2);
v___x_1771_ = l_Lean_NameSet_contains(v_funCC_1770_, v_declName_1730_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_inc(v_declName_1730_);
v___x_1772_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref_known(v___x_1772_, 1);
v___y_1743_ = v_a_1732_;
goto v___jp_1742_;
}
else
{
lean_dec(v___x_1741_);
lean_dec(v_declName_1730_);
lean_dec_ref(v_ext_1729_);
return v___x_1772_;
}
}
else
{
v___y_1743_ = v_a_1732_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v_funCC_1744_; lean_object* v___x_1745_; lean_object* v___f_1746_; lean_object* v___x_1747_; lean_object* v_env_1748_; lean_object* v_nextMacroScope_1749_; lean_object* v_ngen_1750_; lean_object* v_auxDeclNGen_1751_; lean_object* v_traceState_1752_; lean_object* v_recordedDeps_1753_; lean_object* v_messages_1754_; lean_object* v_infoState_1755_; lean_object* v_snapshotTasks_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1768_; 
v_funCC_1744_ = lean_ctor_get(v___x_1741_, 2);
lean_inc(v_funCC_1744_);
lean_dec(v___x_1741_);
v___x_1745_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1730_, v_funCC_1744_);
lean_dec(v_declName_1730_);
v___f_1746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1746_, 0, v___x_1745_);
v___x_1747_ = lean_st_ref_take(v___y_1743_);
v_env_1748_ = lean_ctor_get(v___x_1747_, 0);
v_nextMacroScope_1749_ = lean_ctor_get(v___x_1747_, 1);
v_ngen_1750_ = lean_ctor_get(v___x_1747_, 2);
v_auxDeclNGen_1751_ = lean_ctor_get(v___x_1747_, 3);
v_traceState_1752_ = lean_ctor_get(v___x_1747_, 4);
v_recordedDeps_1753_ = lean_ctor_get(v___x_1747_, 6);
v_messages_1754_ = lean_ctor_get(v___x_1747_, 7);
v_infoState_1755_ = lean_ctor_get(v___x_1747_, 8);
v_snapshotTasks_1756_ = lean_ctor_get(v___x_1747_, 9);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1747_, 5);
lean_dec(v_unused_1769_);
v___x_1758_ = v___x_1747_;
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snapshotTasks_1756_);
lean_inc(v_infoState_1755_);
lean_inc(v_messages_1754_);
lean_inc(v_recordedDeps_1753_);
lean_inc(v_traceState_1752_);
lean_inc(v_auxDeclNGen_1751_);
lean_inc(v_ngen_1750_);
lean_inc(v_nextMacroScope_1749_);
lean_inc(v_env_1748_);
lean_dec(v___x_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1729_, v_env_1748_, v___f_1746_);
v___x_1762_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 5, v___x_1762_);
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_nextMacroScope_1749_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_ngen_1750_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_auxDeclNGen_1751_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_traceState_1752_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1767_, 6, v_recordedDeps_1753_);
lean_ctor_set(v_reuseFailAlloc_1767_, 7, v_messages_1754_);
lean_ctor_set(v_reuseFailAlloc_1767_, 8, v_infoState_1755_);
lean_ctor_set(v_reuseFailAlloc_1767_, 9, v_snapshotTasks_1756_);
v___x_1764_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_st_ref_put(v___y_1743_, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1760_);
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1773_, lean_object* v_declName_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1773_, v_declName_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1779_, lean_object* v_k_1780_, lean_object* v_t_1781_, lean_object* v_h_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1780_, v_t_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1784_, lean_object* v_k_1785_, lean_object* v_t_1786_, lean_object* v_h_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1784_, v_k_1785_, v_t_1786_, v_h_1787_);
lean_dec(v_k_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1789_, lean_object* v_s_1790_){
_start:
{
lean_object* v_casesTypes_1791_; lean_object* v_extThms_1792_; lean_object* v_funCC_1793_; lean_object* v_inj_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_casesTypes_1791_ = lean_ctor_get(v_s_1790_, 0);
v_extThms_1792_ = lean_ctor_get(v_s_1790_, 1);
v_funCC_1793_ = lean_ctor_get(v_s_1790_, 2);
v_inj_1794_ = lean_ctor_get(v_s_1790_, 4);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_s_1790_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_s_1790_, 3);
lean_dec(v_unused_1802_);
v___x_1796_ = v_s_1790_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_inj_1794_);
lean_inc(v_funCC_1793_);
lean_inc(v_extThms_1792_);
lean_inc(v_casesTypes_1791_);
lean_dec(v_s_1790_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 3, v_a_1789_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_casesTypes_1791_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_extThms_1792_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_funCC_1793_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_a_1789_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v_inj_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_1804_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
lean_ctor_set(v___x_1804_, 3, v___x_1803_);
lean_ctor_set(v___x_1804_, 4, v___x_1803_);
lean_ctor_set(v___x_1804_, 5, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1805_, lean_object* v_declName_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_ext_1814_; lean_object* v_toEnvExtension_1815_; lean_object* v_env_1816_; lean_object* v_asyncMode_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v_ematch_1820_; lean_object* v___x_1821_; 
v___x_1812_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1813_ = lean_st_ref_get(v_a_1810_);
v_ext_1814_ = lean_ctor_get(v_ext_1805_, 1);
v_toEnvExtension_1815_ = lean_ctor_get(v_ext_1814_, 0);
v_env_1816_ = lean_ctor_get(v___x_1813_, 0);
lean_inc_ref(v_env_1816_);
lean_dec(v___x_1813_);
v_asyncMode_1817_ = lean_ctor_get(v_toEnvExtension_1815_, 2);
v___x_1818_ = 0;
v___x_1819_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1812_, v_ext_1805_, v_env_1816_, v_asyncMode_1817_, v___x_1818_);
v_ematch_1820_ = lean_ctor_get(v___x_1819_, 3);
lean_inc_ref(v_ematch_1820_);
lean_dec(v___x_1819_);
v___x_1821_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1820_, v_declName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1867_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1867_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1867_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___f_1826_; lean_object* v___x_1827_; lean_object* v_env_1828_; lean_object* v_nextMacroScope_1829_; lean_object* v_ngen_1830_; lean_object* v_auxDeclNGen_1831_; lean_object* v_traceState_1832_; lean_object* v_recordedDeps_1833_; lean_object* v_messages_1834_; lean_object* v_infoState_1835_; lean_object* v_snapshotTasks_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1865_; 
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1826_, 0, v_a_1822_);
v___x_1827_ = lean_st_ref_take(v_a_1810_);
v_env_1828_ = lean_ctor_get(v___x_1827_, 0);
v_nextMacroScope_1829_ = lean_ctor_get(v___x_1827_, 1);
v_ngen_1830_ = lean_ctor_get(v___x_1827_, 2);
v_auxDeclNGen_1831_ = lean_ctor_get(v___x_1827_, 3);
v_traceState_1832_ = lean_ctor_get(v___x_1827_, 4);
v_recordedDeps_1833_ = lean_ctor_get(v___x_1827_, 6);
v_messages_1834_ = lean_ctor_get(v___x_1827_, 7);
v_infoState_1835_ = lean_ctor_get(v___x_1827_, 8);
v_snapshotTasks_1836_ = lean_ctor_get(v___x_1827_, 9);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1827_, 5);
lean_dec(v_unused_1866_);
v___x_1838_ = v___x_1827_;
v_isShared_1839_ = v_isSharedCheck_1865_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_snapshotTasks_1836_);
lean_inc(v_infoState_1835_);
lean_inc(v_messages_1834_);
lean_inc(v_recordedDeps_1833_);
lean_inc(v_traceState_1832_);
lean_inc(v_auxDeclNGen_1831_);
lean_inc(v_ngen_1830_);
lean_inc(v_nextMacroScope_1829_);
lean_inc(v_env_1828_);
lean_dec(v___x_1827_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1865_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1805_, v_env_1828_, v___f_1826_);
v___x_1841_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 5, v___x_1841_);
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_nextMacroScope_1829_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_ngen_1830_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_auxDeclNGen_1831_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_traceState_1832_);
lean_ctor_set(v_reuseFailAlloc_1864_, 5, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1864_, 6, v_recordedDeps_1833_);
lean_ctor_set(v_reuseFailAlloc_1864_, 7, v_messages_1834_);
lean_ctor_set(v_reuseFailAlloc_1864_, 8, v_infoState_1835_);
lean_ctor_set(v_reuseFailAlloc_1864_, 9, v_snapshotTasks_1836_);
v___x_1843_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_mctx_1846_; lean_object* v_zetaDeltaFVarIds_1847_; lean_object* v_postponed_1848_; lean_object* v_diag_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1862_; 
v___x_1844_ = lean_st_ref_put(v_a_1810_, v___x_1843_);
v___x_1845_ = lean_st_ref_take(v_a_1808_);
v_mctx_1846_ = lean_ctor_get(v___x_1845_, 0);
v_zetaDeltaFVarIds_1847_ = lean_ctor_get(v___x_1845_, 2);
v_postponed_1848_ = lean_ctor_get(v___x_1845_, 3);
v_diag_1849_ = lean_ctor_get(v___x_1845_, 4);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1845_, 1);
lean_dec(v_unused_1863_);
v___x_1851_ = v___x_1845_;
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_diag_1849_);
lean_inc(v_postponed_1848_);
lean_inc(v_zetaDeltaFVarIds_1847_);
lean_inc(v_mctx_1846_);
lean_dec(v___x_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1862_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_mctx_1846_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_zetaDeltaFVarIds_1847_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_postponed_1848_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_diag_1849_);
v___x_1856_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1857_ = lean_st_ref_put(v_a_1808_, v___x_1856_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1853_);
v___x_1859_ = v___x_1824_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1853_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_ext_1805_);
v_a_1868_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1821_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1821_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1876_, lean_object* v_declName_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1876_, v_declName_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1884_, lean_object* v_s_1885_){
_start:
{
lean_object* v_casesTypes_1886_; lean_object* v_extThms_1887_; lean_object* v_funCC_1888_; lean_object* v_ematch_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_casesTypes_1886_ = lean_ctor_get(v_s_1885_, 0);
v_extThms_1887_ = lean_ctor_get(v_s_1885_, 1);
v_funCC_1888_ = lean_ctor_get(v_s_1885_, 2);
v_ematch_1889_ = lean_ctor_get(v_s_1885_, 3);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_s_1885_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v_s_1885_, 4);
lean_dec(v_unused_1897_);
v___x_1891_ = v_s_1885_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_ematch_1889_);
lean_inc(v_funCC_1888_);
lean_inc(v_extThms_1887_);
lean_inc(v_casesTypes_1886_);
lean_dec(v_s_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_a_1884_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_casesTypes_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_extThms_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_funCC_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_ematch_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_a_1884_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1898_, lean_object* v_declName_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_ext_1907_; lean_object* v_toEnvExtension_1908_; lean_object* v_env_1909_; lean_object* v_asyncMode_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v_inj_1913_; lean_object* v___x_1914_; 
v___x_1905_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1906_ = lean_st_ref_get(v_a_1903_);
v_ext_1907_ = lean_ctor_get(v_ext_1898_, 1);
v_toEnvExtension_1908_ = lean_ctor_get(v_ext_1907_, 0);
v_env_1909_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_env_1909_);
lean_dec(v___x_1906_);
v_asyncMode_1910_ = lean_ctor_get(v_toEnvExtension_1908_, 2);
v___x_1911_ = 0;
v___x_1912_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1905_, v_ext_1898_, v_env_1909_, v_asyncMode_1910_, v___x_1911_);
v_inj_1913_ = lean_ctor_get(v___x_1912_, 4);
lean_inc_ref(v_inj_1913_);
lean_dec(v___x_1912_);
v___x_1914_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1913_, v_declName_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1960_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1960_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1960_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v_env_1921_; lean_object* v_nextMacroScope_1922_; lean_object* v_ngen_1923_; lean_object* v_auxDeclNGen_1924_; lean_object* v_traceState_1925_; lean_object* v_recordedDeps_1926_; lean_object* v_messages_1927_; lean_object* v_infoState_1928_; lean_object* v_snapshotTasks_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1958_; 
v___f_1919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1919_, 0, v_a_1915_);
v___x_1920_ = lean_st_ref_take(v_a_1903_);
v_env_1921_ = lean_ctor_get(v___x_1920_, 0);
v_nextMacroScope_1922_ = lean_ctor_get(v___x_1920_, 1);
v_ngen_1923_ = lean_ctor_get(v___x_1920_, 2);
v_auxDeclNGen_1924_ = lean_ctor_get(v___x_1920_, 3);
v_traceState_1925_ = lean_ctor_get(v___x_1920_, 4);
v_recordedDeps_1926_ = lean_ctor_get(v___x_1920_, 6);
v_messages_1927_ = lean_ctor_get(v___x_1920_, 7);
v_infoState_1928_ = lean_ctor_get(v___x_1920_, 8);
v_snapshotTasks_1929_ = lean_ctor_get(v___x_1920_, 9);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v___x_1920_, 5);
lean_dec(v_unused_1959_);
v___x_1931_ = v___x_1920_;
v_isShared_1932_ = v_isSharedCheck_1958_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_snapshotTasks_1929_);
lean_inc(v_infoState_1928_);
lean_inc(v_messages_1927_);
lean_inc(v_recordedDeps_1926_);
lean_inc(v_traceState_1925_);
lean_inc(v_auxDeclNGen_1924_);
lean_inc(v_ngen_1923_);
lean_inc(v_nextMacroScope_1922_);
lean_inc(v_env_1921_);
lean_dec(v___x_1920_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1958_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1933_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1898_, v_env_1921_, v___f_1919_);
v___x_1934_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 5, v___x_1934_);
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1922_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1923_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1924_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_traceState_1925_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_recordedDeps_1926_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_messages_1927_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_infoState_1928_);
lean_ctor_set(v_reuseFailAlloc_1957_, 9, v_snapshotTasks_1929_);
v___x_1936_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v_mctx_1939_; lean_object* v_zetaDeltaFVarIds_1940_; lean_object* v_postponed_1941_; lean_object* v_diag_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1955_; 
v___x_1937_ = lean_st_ref_put(v_a_1903_, v___x_1936_);
v___x_1938_ = lean_st_ref_take(v_a_1901_);
v_mctx_1939_ = lean_ctor_get(v___x_1938_, 0);
v_zetaDeltaFVarIds_1940_ = lean_ctor_get(v___x_1938_, 2);
v_postponed_1941_ = lean_ctor_get(v___x_1938_, 3);
v_diag_1942_ = lean_ctor_get(v___x_1938_, 4);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1938_, 1);
lean_dec(v_unused_1956_);
v___x_1944_ = v___x_1938_;
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_diag_1942_);
lean_inc(v_postponed_1941_);
lean_inc(v_zetaDeltaFVarIds_1940_);
lean_inc(v_mctx_1939_);
lean_dec(v___x_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v___x_1947_);
v___x_1949_ = v___x_1944_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_mctx_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_zetaDeltaFVarIds_1940_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_postponed_1941_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_diag_1942_);
v___x_1949_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_put(v_a_1901_, v___x_1949_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1946_);
v___x_1952_ = v___x_1917_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1946_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_ext_1898_);
v_a_1961_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1914_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1914_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1969_, lean_object* v_declName_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1969_, v_declName_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1977_, lean_object* v_i_1978_, lean_object* v_k_1979_){
_start:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = lean_array_get_size(v_keys_1977_);
v___x_1981_ = lean_nat_dec_lt(v_i_1978_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec(v_i_1978_);
return v___x_1981_;
}
else
{
lean_object* v_k_x27_1982_; uint8_t v___x_1983_; 
v_k_x27_1982_ = lean_array_fget_borrowed(v_keys_1977_, v_i_1978_);
v___x_1983_ = lean_name_eq(v_k_1979_, v_k_x27_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_add(v_i_1978_, v___x_1984_);
lean_dec(v_i_1978_);
v_i_1978_ = v___x_1985_;
goto _start;
}
else
{
lean_dec(v_i_1978_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1987_, lean_object* v_i_1988_, lean_object* v_k_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1987_, v_i_1988_, v_k_1989_);
lean_dec(v_k_1989_);
lean_dec_ref(v_keys_1987_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1992_, size_t v_x_1993_, lean_object* v_x_1994_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_object* v_es_1995_; lean_object* v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; lean_object* v_j_1999_; lean_object* v___x_2000_; 
v_es_1995_ = lean_ctor_get(v_x_1992_, 0);
v___x_1996_ = lean_box(2);
v___x_1997_ = ((size_t)31ULL);
v___x_1998_ = lean_usize_land(v_x_1993_, v___x_1997_);
v_j_1999_ = lean_usize_to_nat(v___x_1998_);
v___x_2000_ = lean_array_get_borrowed(v___x_1996_, v_es_1995_, v_j_1999_);
lean_dec(v_j_1999_);
switch(lean_obj_tag(v___x_2000_))
{
case 0:
{
lean_object* v_key_2001_; uint8_t v___x_2002_; 
v_key_2001_ = lean_ctor_get(v___x_2000_, 0);
v___x_2002_ = lean_name_eq(v_x_1994_, v_key_2001_);
return v___x_2002_;
}
case 1:
{
lean_object* v_node_2003_; size_t v___x_2004_; size_t v___x_2005_; 
v_node_2003_ = lean_ctor_get(v___x_2000_, 0);
v___x_2004_ = ((size_t)5ULL);
v___x_2005_ = lean_usize_shift_right(v_x_1993_, v___x_2004_);
v_x_1992_ = v_node_2003_;
v_x_1993_ = v___x_2005_;
goto _start;
}
default: 
{
uint8_t v___x_2007_; 
v___x_2007_ = 0;
return v___x_2007_;
}
}
}
else
{
lean_object* v_ks_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_ks_2008_ = lean_ctor_get(v_x_1992_, 0);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_2008_, v___x_2009_, v_x_1994_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
size_t v_x_330__boxed_2014_; uint8_t v_res_2015_; lean_object* v_r_2016_; 
v_x_330__boxed_2014_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_res_2015_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2011_, v_x_330__boxed_2014_, v_x_2013_);
lean_dec(v_x_2013_);
lean_dec_ref(v_x_2011_);
v_r_2016_ = lean_box(v_res_2015_);
return v_r_2016_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
uint64_t v___y_2020_; 
if (lean_obj_tag(v_x_2018_) == 0)
{
uint64_t v___x_2023_; 
v___x_2023_ = 1723ULL;
v___y_2020_ = v___x_2023_;
goto v___jp_2019_;
}
else
{
uint64_t v_hash_2024_; 
v_hash_2024_ = lean_ctor_get_uint64(v_x_2018_, sizeof(void*)*2);
v___y_2020_ = v_hash_2024_;
goto v___jp_2019_;
}
v___jp_2019_:
{
size_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_uint64_to_usize(v___y_2020_);
v___x_2022_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2017_, v___x_2021_, v_x_2018_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
uint8_t v_res_2027_; lean_object* v_r_2028_; 
v_res_2027_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2025_, v_x_2026_);
lean_dec(v_x_2026_);
lean_dec_ref(v_x_2025_);
v_r_2028_ = lean_box(v_res_2027_);
return v_r_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2029_, lean_object* v_declName_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_ext_2035_; lean_object* v_toEnvExtension_2036_; lean_object* v_env_2037_; lean_object* v_asyncMode_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v_extThms_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2033_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2034_ = lean_st_ref_get(v_a_2031_);
v_ext_2035_ = lean_ctor_get(v_ext_2029_, 1);
v_toEnvExtension_2036_ = lean_ctor_get(v_ext_2035_, 0);
v_env_2037_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_env_2037_);
lean_dec(v___x_2034_);
v_asyncMode_2038_ = lean_ctor_get(v_toEnvExtension_2036_, 2);
v___x_2039_ = 0;
v___x_2040_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2033_, v_ext_2029_, v_env_2037_, v_asyncMode_2038_, v___x_2039_);
v_extThms_2041_ = lean_ctor_get(v___x_2040_, 1);
lean_inc_ref(v_extThms_2041_);
lean_dec(v___x_2040_);
v___x_2042_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2041_, v_declName_2030_);
lean_dec_ref(v_extThms_2041_);
v___x_2043_ = lean_box(v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2045_, lean_object* v_declName_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2045_, v_declName_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec(v_declName_2046_);
lean_dec_ref(v_ext_2045_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2050_, lean_object* v_declName_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2050_, v_declName_2051_, v_a_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2056_, lean_object* v_declName_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2056_, v_declName_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_declName_2057_);
lean_dec_ref(v_ext_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
uint8_t v___x_2065_; 
v___x_2065_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2063_, v_x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
uint8_t v_res_2069_; lean_object* v_r_2070_; 
v_res_2069_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2066_, v_x_2067_, v_x_2068_);
lean_dec(v_x_2068_);
lean_dec_ref(v_x_2067_);
v_r_2070_ = lean_box(v_res_2069_);
return v_r_2070_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2071_, lean_object* v_x_2072_, size_t v_x_2073_, lean_object* v_x_2074_){
_start:
{
uint8_t v___x_2075_; 
v___x_2075_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2072_, v_x_2073_, v_x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
size_t v_x_417__boxed_2080_; uint8_t v_res_2081_; lean_object* v_r_2082_; 
v_x_417__boxed_2080_ = lean_unbox_usize(v_x_2078_);
lean_dec(v_x_2078_);
v_res_2081_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2076_, v_x_2077_, v_x_417__boxed_2080_, v_x_2079_);
lean_dec(v_x_2079_);
lean_dec_ref(v_x_2077_);
v_r_2082_ = lean_box(v_res_2081_);
return v_r_2082_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2083_, lean_object* v_keys_2084_, lean_object* v_vals_2085_, lean_object* v_heq_2086_, lean_object* v_i_2087_, lean_object* v_k_2088_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2084_, v_i_2087_, v_k_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2090_, lean_object* v_keys_2091_, lean_object* v_vals_2092_, lean_object* v_heq_2093_, lean_object* v_i_2094_, lean_object* v_k_2095_){
_start:
{
uint8_t v_res_2096_; lean_object* v_r_2097_; 
v_res_2096_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2090_, v_keys_2091_, v_vals_2092_, v_heq_2093_, v_i_2094_, v_k_2095_);
lean_dec(v_k_2095_);
lean_dec_ref(v_vals_2092_);
lean_dec_ref(v_keys_2091_);
v_r_2097_ = lean_box(v_res_2096_);
return v_r_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2098_, lean_object* v_declName_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_ext_2104_; lean_object* v_toEnvExtension_2105_; lean_object* v_env_2106_; lean_object* v_asyncMode_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v_inj_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2102_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2103_ = lean_st_ref_get(v_a_2100_);
v_ext_2104_ = lean_ctor_get(v_ext_2098_, 1);
v_toEnvExtension_2105_ = lean_ctor_get(v_ext_2104_, 0);
v_env_2106_ = lean_ctor_get(v___x_2103_, 0);
lean_inc_ref(v_env_2106_);
lean_dec(v___x_2103_);
v_asyncMode_2107_ = lean_ctor_get(v_toEnvExtension_2105_, 2);
v___x_2108_ = 0;
v___x_2109_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2102_, v_ext_2098_, v_env_2106_, v_asyncMode_2107_, v___x_2108_);
v_inj_2110_ = lean_ctor_get(v___x_2109_, 4);
lean_inc_ref(v_inj_2110_);
lean_dec(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_declName_2099_);
v___x_2112_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2110_, v___x_2111_);
lean_dec_ref_known(v___x_2111_, 1);
lean_dec_ref(v_inj_2110_);
v___x_2113_ = lean_box(v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2115_, lean_object* v_declName_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2115_, v_declName_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_ext_2115_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2120_, lean_object* v_declName_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2120_, v_declName_2121_, v_a_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2126_, lean_object* v_declName_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2126_, v_declName_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_ext_2126_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2132_, lean_object* v_declName_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v_ext_2138_; lean_object* v_toEnvExtension_2139_; lean_object* v_env_2140_; lean_object* v_asyncMode_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v_funCC_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2136_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2137_ = lean_st_ref_get(v_a_2134_);
v_ext_2138_ = lean_ctor_get(v_ext_2132_, 1);
v_toEnvExtension_2139_ = lean_ctor_get(v_ext_2138_, 0);
v_env_2140_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_env_2140_);
lean_dec(v___x_2137_);
v_asyncMode_2141_ = lean_ctor_get(v_toEnvExtension_2139_, 2);
v___x_2142_ = 0;
v___x_2143_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2136_, v_ext_2132_, v_env_2140_, v_asyncMode_2141_, v___x_2142_);
v_funCC_2144_ = lean_ctor_get(v___x_2143_, 2);
lean_inc(v_funCC_2144_);
lean_dec(v___x_2143_);
v___x_2145_ = l_Lean_NameSet_contains(v_funCC_2144_, v_declName_2133_);
lean_dec(v_funCC_2144_);
v___x_2146_ = lean_box(v___x_2145_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2148_, lean_object* v_declName_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2148_, v_declName_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_ext_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2153_, lean_object* v_declName_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2153_, v_declName_2154_, v_a_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2159_, lean_object* v_declName_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2159_, v_declName_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_declName_2160_);
lean_dec_ref(v_ext_2159_);
return v_res_2164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2189_ = l_Lean_mkAtom(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2202_ = l_Lean_mkAtom(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2208_ = lean_box(2);
v___x_2209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2215_ = lean_box(2);
v___x_2216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2213_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2222_ = lean_box(2);
v___x_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2220_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2229_ = lean_box(2);
v___x_2230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2228_);
lean_ctor_set(v___x_2230_, 2, v___x_2227_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2233_ = lean_array_push(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2236_ = lean_box(2);
v___x_2237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2235_);
lean_ctor_set(v___x_2237_, 2, v___x_2234_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2239_, lean_object* v_ext_2240_, lean_object* v_____r_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
uint8_t v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = 0;
lean_inc(v_declName_2239_);
v___x_2248_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2239_, v___x_2247_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; uint8_t v___x_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = lean_unbox(v_a_2249_);
lean_dec(v_a_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v_a_2252_; uint8_t v___x_2253_; 
v___x_2251_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v_a_2255_; uint8_t v___x_2256_; 
lean_inc(v_declName_2239_);
v___x_2254_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v_a_2258_; uint8_t v___x_2259_; 
v___x_2257_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2240_, v_declName_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2261_;
}
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2240_, v_declName_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2262_;
}
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2263_;
}
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v_ext_2240_);
lean_dec(v_declName_2239_);
v_a_2265_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2248_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2248_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2273_, lean_object* v_ext_2274_, lean_object* v_____r_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2273_, v_ext_2274_, v_____r_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v_env_2289_; uint8_t v___x_2290_; lean_object* v_env_2291_; lean_object* v___x_2292_; lean_object* v_toCold_2293_; lean_object* v_mctx_2294_; lean_object* v_lctx_2295_; lean_object* v_options_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2288_ = lean_st_ref_get(v___y_2286_);
v_env_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_ref(v_env_2289_);
lean_dec(v___x_2288_);
v___x_2290_ = 0;
v_env_2291_ = l_Lean_Environment_setRecordingDeps(v_env_2289_, v___x_2290_);
v___x_2292_ = lean_st_ref_get(v___y_2284_);
v_toCold_2293_ = lean_ctor_get(v___y_2285_, 0);
v_mctx_2294_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_ref(v_mctx_2294_);
lean_dec(v___x_2292_);
v_lctx_2295_ = lean_ctor_get(v___y_2283_, 2);
v_options_2296_ = lean_ctor_get(v_toCold_2293_, 2);
lean_inc_ref(v_options_2296_);
lean_inc_ref(v_lctx_2295_);
v___x_2297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2297_, 0, v_env_2291_);
lean_ctor_set(v___x_2297_, 1, v_mctx_2294_);
lean_ctor_set(v___x_2297_, 2, v_lctx_2295_);
lean_ctor_set(v___x_2297_, 3, v_options_2296_);
v___x_2298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v_msgData_2282_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_ref_2313_; lean_object* v___x_2314_; lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
v_ref_2313_ = lean_ctor_get(v___y_2310_, 2);
v___x_2314_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
lean_inc(v_ref_2313_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_ref_2313_);
lean_ctor_set(v___x_2319_, 1, v_a_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 1);
lean_ctor_set(v___x_2317_, 0, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2330_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2337_; uint64_t v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set_uint64(v___x_2341_, sizeof(void*)*1, v___x_2339_);
return v___x_2341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2344_ = lean_box(1);
v___x_2345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2346_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set(v___x_2347_, 1, v___x_2345_);
lean_ctor_set(v___x_2347_, 2, v___x_2344_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
lean_ctor_set(v___x_2353_, 2, v___x_2352_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
lean_ctor_set(v___x_2353_, 4, v___x_2351_);
lean_ctor_set(v___x_2353_, 5, v___x_2351_);
lean_ctor_set(v___x_2353_, 6, v___x_2351_);
lean_ctor_set(v___x_2353_, 7, v___x_2351_);
lean_ctor_set(v___x_2353_, 8, v___x_2351_);
lean_ctor_set(v___x_2353_, 9, v___x_2351_);
lean_ctor_set(v___x_2353_, 10, v___x_2351_);
lean_ctor_set(v___x_2353_, 11, v___x_2350_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2355_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
lean_ctor_set(v___x_2355_, 2, v___x_2354_);
lean_ctor_set(v___x_2355_, 3, v___x_2354_);
lean_ctor_set(v___x_2355_, 4, v___x_2354_);
lean_ctor_set(v___x_2355_, 5, v___x_2354_);
return v___x_2355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
lean_ctor_set(v___x_2357_, 2, v___x_2356_);
lean_ctor_set(v___x_2357_, 3, v___x_2356_);
lean_ctor_set(v___x_2357_, 4, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_2360_ = l_Lean_stringToMessageData(v___x_2359_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_2366_ = l_Lean_stringToMessageData(v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_2367_, lean_object* v___x_2368_, uint8_t v_showInfo_2369_, lean_object* v_attrName_2370_, lean_object* v_declName_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___y_2390_; 
v___x_2375_ = 1;
v___x_2376_ = 0;
v___x_2377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_2382_ = lean_box(0);
lean_inc(v___x_2368_);
v___x_2383_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2383_, 0, v___x_2377_);
lean_ctor_set(v___x_2383_, 1, v___x_2368_);
lean_ctor_set(v___x_2383_, 2, v___x_2380_);
lean_ctor_set(v___x_2383_, 3, v___x_2381_);
lean_ctor_set(v___x_2383_, 4, v___x_2382_);
lean_ctor_set(v___x_2383_, 5, v___x_2378_);
lean_ctor_set(v___x_2383_, 6, v___x_2382_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7, v___x_2376_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 1, v___x_2376_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 2, v___x_2376_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 3, v___x_2375_);
v___x_2384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_2385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2384_);
lean_ctor_set(v___x_2387_, 1, v___x_2385_);
lean_ctor_set(v___x_2387_, 2, v___x_2368_);
lean_ctor_set(v___x_2387_, 3, v___x_2379_);
lean_ctor_set(v___x_2387_, 4, v___x_2386_);
v___x_2388_ = lean_st_mk_ref(v___x_2387_);
if (v_showInfo_2369_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec(v_attrName_2370_);
v___x_2400_ = lean_box(0);
v___x_2401_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2371_, v_ext_2367_, v___x_2400_, v___x_2383_, v___x_2388_, v___y_2372_, v___y_2373_);
lean_dec_ref_known(v___x_2383_, 7);
v___y_2390_ = v___x_2401_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_declName_2371_);
lean_dec_ref(v_ext_2367_);
v___x_2402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_2403_ = l_Lean_MessageData_ofName(v_attrName_2370_);
lean_inc_ref(v___x_2403_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2403_);
v___x_2408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2409_, v___x_2383_, v___x_2388_, v___y_2372_, v___y_2373_);
lean_dec_ref_known(v___x_2383_, 7);
v___y_2390_ = v___x_2410_;
goto v___jp_2389_;
}
v___jp_2389_:
{
if (lean_obj_tag(v___y_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_a_2391_ = lean_ctor_get(v___y_2390_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___y_2390_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v___y_2390_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___y_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_st_ref_get(v___x_2388_);
lean_dec(v___x_2388_);
lean_dec(v___x_2395_);
if (v_isShared_2394_ == 0)
{
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2391_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
else
{
lean_dec(v___x_2388_);
return v___y_2390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_2411_, lean_object* v___x_2412_, lean_object* v_showInfo_2413_, lean_object* v_attrName_2414_, lean_object* v_declName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v_showInfo_boxed_2419_; lean_object* v_res_2420_; 
v_showInfo_boxed_2419_ = lean_unbox(v_showInfo_2413_);
v_res_2420_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_2411_, v___x_2412_, v_showInfo_boxed_2419_, v_attrName_2414_, v_declName_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2423_, uint8_t v_attrKind_2424_, uint8_t v_showInfo_2425_, uint8_t v_minIndexable_2426_, lean_object* v_as_x27_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
if (lean_obj_tag(v_as_x27_2427_) == 0)
{
lean_object* v___x_2434_; 
lean_dec_ref(v_ext_2423_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_b_2428_);
return v___x_2434_;
}
else
{
lean_object* v_head_2435_; lean_object* v_tail_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_head_2435_ = lean_ctor_get(v_as_x27_2427_, 0);
v_tail_2436_ = lean_ctor_get(v_as_x27_2427_, 1);
v___x_2437_ = lean_box(0);
v___x_2438_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2432_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2435_);
lean_inc_ref(v_ext_2423_);
v___x_2441_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2423_, v_head_2435_, v_attrKind_2424_, v___x_2440_, v_a_2439_, v_showInfo_2425_, v_minIndexable_2426_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_dec_ref_known(v___x_2441_, 1);
v_as_x27_2427_ = v_tail_2436_;
v_b_2428_ = v___x_2437_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2423_);
return v___x_2441_;
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_ext_2423_);
v_a_2443_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2438_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2438_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2451_, lean_object* v_attrKind_2452_, lean_object* v_showInfo_2453_, lean_object* v_minIndexable_2454_, lean_object* v_as_x27_2455_, lean_object* v_b_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v_attrKind_boxed_2462_; uint8_t v_showInfo_boxed_2463_; uint8_t v_minIndexable_boxed_2464_; lean_object* v_res_2465_; 
v_attrKind_boxed_2462_ = lean_unbox(v_attrKind_2452_);
v_showInfo_boxed_2463_ = lean_unbox(v_showInfo_2453_);
v_minIndexable_boxed_2464_ = lean_unbox(v_minIndexable_2454_);
v_res_2465_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2451_, v_attrKind_boxed_2462_, v_showInfo_boxed_2463_, v_minIndexable_boxed_2464_, v_as_x27_2455_, v_b_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v_as_x27_2455_);
return v_res_2465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_2496_, uint8_t v___x_2497_, uint8_t v_attrKind_2498_, lean_object* v_stx_2499_, lean_object* v_ext_2500_, uint8_t v_showInfo_2501_, uint8_t v_minIndexable_2502_, lean_object* v_attrName_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2499_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
switch(lean_obj_tag(v_a_2534_))
{
case 0:
{
lean_object* v_k_2535_; 
lean_dec(v_attrName_2503_);
lean_dec(v_stx_2499_);
v_k_2535_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_k_2535_);
lean_dec_ref_known(v_a_2534_, 1);
if (lean_obj_tag(v_k_2535_) == 9)
{
lean_object* v___x_2536_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_declName_2496_);
v___x_2536_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2506_, v___y_2507_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2507_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2500_, v_declName_2496_, v_attrKind_2498_, v_k_2535_, v_a_2538_, v_showInfo_2501_, v_minIndexable_2502_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2539_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_k_2535_);
lean_dec_ref(v_ext_2500_);
lean_dec(v_declName_2496_);
v_a_2540_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2537_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2548_; lean_object* v___x_2549_; 
lean_dec(v_attrName_2503_);
lean_dec(v_stx_2499_);
v_eager_2548_ = lean_ctor_get_uint8(v_a_2534_, 0);
lean_dec_ref_known(v_a_2534_, 0);
v___x_2549_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2500_, v_declName_2496_, v_eager_2548_, v_attrKind_2498_, v___y_2506_, v___y_2507_);
return v___x_2549_;
}
case 2:
{
lean_object* v___x_2550_; 
lean_dec(v_stx_2499_);
lean_inc(v_declName_2496_);
v___x_2550_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2496_, v___x_2497_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
if (lean_obj_tag(v_a_2551_) == 1)
{
lean_object* v_val_2552_; lean_object* v_ctors_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_attrName_2503_);
lean_dec(v_declName_2496_);
v_val_2552_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_a_2551_, 1);
v_ctors_2553_ = lean_ctor_get(v_val_2552_, 4);
lean_inc(v_ctors_2553_);
lean_dec(v_val_2552_);
v___x_2554_ = lean_box(0);
v___x_2555_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2500_, v_attrKind_2498_, v_showInfo_2501_, v_minIndexable_2502_, v_ctors_2553_, v___x_2554_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v_ctors_2553_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2563_);
v___x_2557_ = v___x_2555_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v___x_2555_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2554_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2554_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
return v___x_2555_;
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec(v_a_2551_);
lean_dec_ref(v_ext_2500_);
v___x_2564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2565_ = l_Lean_MessageData_ofName(v_attrName_2503_);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l_Lean_MessageData_ofConstName(v_declName_2496_, v___x_2497_);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2572_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2573_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_attrName_2503_);
lean_dec_ref(v_ext_2500_);
lean_dec(v_declName_2496_);
v_a_2574_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2550_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2550_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
case 3:
{
lean_object* v___x_2582_; 
lean_dec(v_attrName_2503_);
lean_inc(v_declName_2496_);
v___x_2582_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2496_, v___x_2497_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
if (lean_obj_tag(v_a_2583_) == 1)
{
lean_object* v_val_2584_; lean_object* v___x_2585_; 
lean_dec(v_stx_2499_);
lean_dec(v_declName_2496_);
v_val_2584_ = lean_ctor_get(v_a_2583_, 0);
lean_inc_n(v_val_2584_, 2);
lean_dec_ref_known(v_a_2583_, 1);
lean_inc_ref(v_ext_2500_);
v___x_2585_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2500_, v_val_2584_, v___x_2497_, v_attrKind_2498_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref_known(v___x_2585_, 1);
v___x_2586_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2584_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2607_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2607_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
if (lean_obj_tag(v_a_2587_) == 1)
{
lean_object* v_val_2591_; lean_object* v_ctors_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2589_);
v_val_2591_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v_a_2587_, 1);
v_ctors_2592_ = lean_ctor_get(v_val_2591_, 4);
lean_inc(v_ctors_2592_);
lean_dec(v_val_2591_);
v___x_2593_ = lean_box(0);
v___x_2594_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2500_, v_attrKind_2498_, v_showInfo_2501_, v_minIndexable_2502_, v_ctors_2592_, v___x_2593_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v_ctors_2592_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2594_, 0);
lean_dec(v_unused_2602_);
v___x_2596_ = v___x_2594_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_dec(v___x_2594_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2593_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2593_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec(v_a_2587_);
lean_dec_ref(v_ext_2500_);
v___x_2603_ = lean_box(0);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2603_);
v___x_2605_ = v___x_2589_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v_ext_2500_);
v_a_2608_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2586_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2586_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_dec(v_val_2584_);
lean_dec_ref(v_ext_2500_);
return v___x_2585_;
}
}
else
{
lean_object* v___x_2616_; 
lean_dec(v_a_2583_);
v___x_2616_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2507_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2500_, v_stx_2499_, v_declName_2496_, v_attrKind_2498_, v_a_2617_, v_minIndexable_2502_, v_showInfo_2501_, v___x_2497_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2618_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
lean_dec(v_declName_2496_);
v_a_2619_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2616_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2616_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
lean_dec(v_declName_2496_);
v_a_2627_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2582_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2582_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
case 4:
{
lean_object* v___x_2635_; 
lean_dec(v_attrName_2503_);
lean_dec(v_stx_2499_);
v___x_2635_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2500_, v_declName_2496_, v_attrKind_2498_, v___y_2506_, v___y_2507_);
return v___x_2635_;
}
case 5:
{
lean_object* v_prio_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
v_prio_2636_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_prio_2636_);
lean_dec_ref_known(v_a_2534_, 1);
v___x_2637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2638_ = lean_name_eq(v_attrName_2503_, v___x_2637_);
lean_dec(v_attrName_2503_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec(v_prio_2636_);
lean_dec(v_declName_2496_);
v___x_2639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2640_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2639_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2496_, v_attrKind_2498_, v_prio_2636_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2641_;
}
}
case 6:
{
lean_object* v___x_2642_; 
lean_dec(v_attrName_2503_);
lean_dec(v_stx_2499_);
v___x_2642_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2500_, v_declName_2496_, v_attrKind_2498_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2642_;
}
case 7:
{
lean_object* v___x_2643_; 
lean_dec(v_attrName_2503_);
lean_dec(v_stx_2499_);
v___x_2643_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2500_, v_declName_2496_, v_attrKind_2498_, v___y_2506_, v___y_2507_);
return v___x_2643_;
}
case 8:
{
uint8_t v_post_2644_; uint8_t v_inv_2645_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
v_post_2644_ = lean_ctor_get_uint8(v_a_2534_, 0);
v_inv_2645_ = lean_ctor_get_uint8(v_a_2534_, 1);
lean_dec_ref_known(v_a_2534_, 0);
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2655_ = lean_name_eq(v_attrName_2503_, v___x_2654_);
lean_dec(v_attrName_2503_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec(v_declName_2496_);
v___x_2656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2657_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2656_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2657_;
}
else
{
v___y_2647_ = v___y_2504_;
v___y_2648_ = v___y_2505_;
v___y_2649_ = v___y_2506_;
v___y_2650_ = v___y_2507_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = l_Lean_Meta_Grind_normExt;
v___x_2652_ = lean_unsigned_to_nat(1000u);
v___x_2653_ = l_Lean_Meta_addSimpTheorem(v___x_2651_, v_declName_2496_, v_post_2644_, v_inv_2645_, v_attrKind_2498_, v___x_2652_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2653_;
}
}
case 9:
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2659_ = lean_name_eq(v_attrName_2503_, v___x_2658_);
lean_dec(v_attrName_2503_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v_declName_2496_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2661_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2660_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2661_;
}
else
{
goto v___jp_2509_;
}
}
case 10:
{
uint8_t v_fallback_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
v_fallback_2662_ = lean_ctor_get_uint8(v_a_2534_, 0);
lean_dec_ref_known(v_a_2534_, 0);
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2664_ = lean_name_eq(v_attrName_2503_, v___x_2663_);
lean_dec(v_attrName_2503_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_declName_2496_);
v___x_2665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2666_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2665_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2496_, v_attrKind_2498_, v_fallback_2662_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2667_;
}
}
default: 
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
v___x_2668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2669_ = lean_name_eq(v_attrName_2503_, v___x_2668_);
lean_dec(v_attrName_2503_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec(v_declName_2496_);
v___x_2670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2671_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2670_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2671_;
}
else
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2496_, v_attrKind_2498_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_attrName_2503_);
lean_dec_ref(v_ext_2500_);
lean_dec(v_stx_2499_);
lean_dec(v_declName_2496_);
v_a_2673_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2533_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2533_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
v___jp_2509_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_Meta_Grind_normExt;
v___x_2511_ = lean_unsigned_to_nat(1000u);
v___x_2512_ = l_Lean_Meta_addDeclToUnfold(v___x_2510_, v_declName_2496_, v___x_2497_, v___x_2497_, v___x_2511_, v_attrKind_2498_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2524_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2524_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2524_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_del_object(v___x_2515_);
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2519_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2518_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2520_);
v___x_2522_ = v___x_2515_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_a_2525_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2512_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2512_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_2681_, lean_object* v___x_2682_, lean_object* v_attrKind_2683_, lean_object* v_stx_2684_, lean_object* v_ext_2685_, lean_object* v_showInfo_2686_, lean_object* v_minIndexable_2687_, lean_object* v_attrName_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___x_15286__boxed_2694_; uint8_t v_attrKind_boxed_2695_; uint8_t v_showInfo_boxed_2696_; uint8_t v_minIndexable_boxed_2697_; lean_object* v_res_2698_; 
v___x_15286__boxed_2694_ = lean_unbox(v___x_2682_);
v_attrKind_boxed_2695_ = lean_unbox(v_attrKind_2683_);
v_showInfo_boxed_2696_ = lean_unbox(v_showInfo_2686_);
v_minIndexable_boxed_2697_ = lean_unbox(v_minIndexable_2687_);
v_res_2698_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_2681_, v___x_15286__boxed_2694_, v_attrKind_boxed_2695_, v_stx_2684_, v_ext_2685_, v_showInfo_boxed_2696_, v_minIndexable_boxed_2697_, v_attrName_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2698_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2699_; double v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = lean_float_of_nat(v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_ref_2711_; lean_object* v___x_2712_; lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2758_; 
v_ref_2711_ = lean_ctor_get(v___y_2708_, 2);
v___x_2712_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2758_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2758_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v_traceState_2718_; lean_object* v_env_2719_; lean_object* v_nextMacroScope_2720_; lean_object* v_ngen_2721_; lean_object* v_auxDeclNGen_2722_; lean_object* v_cache_2723_; lean_object* v_recordedDeps_2724_; lean_object* v_messages_2725_; lean_object* v_infoState_2726_; lean_object* v_snapshotTasks_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2757_; 
v___x_2717_ = lean_st_ref_take(v___y_2709_);
v_traceState_2718_ = lean_ctor_get(v___x_2717_, 4);
v_env_2719_ = lean_ctor_get(v___x_2717_, 0);
v_nextMacroScope_2720_ = lean_ctor_get(v___x_2717_, 1);
v_ngen_2721_ = lean_ctor_get(v___x_2717_, 2);
v_auxDeclNGen_2722_ = lean_ctor_get(v___x_2717_, 3);
v_cache_2723_ = lean_ctor_get(v___x_2717_, 5);
v_recordedDeps_2724_ = lean_ctor_get(v___x_2717_, 6);
v_messages_2725_ = lean_ctor_get(v___x_2717_, 7);
v_infoState_2726_ = lean_ctor_get(v___x_2717_, 8);
v_snapshotTasks_2727_ = lean_ctor_get(v___x_2717_, 9);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2729_ = v___x_2717_;
v_isShared_2730_ = v_isSharedCheck_2757_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_snapshotTasks_2727_);
lean_inc(v_infoState_2726_);
lean_inc(v_messages_2725_);
lean_inc(v_recordedDeps_2724_);
lean_inc(v_cache_2723_);
lean_inc(v_traceState_2718_);
lean_inc(v_auxDeclNGen_2722_);
lean_inc(v_ngen_2721_);
lean_inc(v_nextMacroScope_2720_);
lean_inc(v_env_2719_);
lean_dec(v___x_2717_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2757_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
uint64_t v_tid_2731_; lean_object* v_traces_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2756_; 
v_tid_2731_ = lean_ctor_get_uint64(v_traceState_2718_, sizeof(void*)*1);
v_traces_2732_ = lean_ctor_get(v_traceState_2718_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_traceState_2718_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2734_ = v_traceState_2718_;
v_isShared_2735_ = v_isSharedCheck_2756_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_traces_2732_);
lean_dec(v_traceState_2718_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2756_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; double v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_box(0);
v___x_2738_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2739_ = 0;
v___x_2740_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2741_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2741_, 0, v_cls_2704_);
lean_ctor_set(v___x_2741_, 1, v___x_2737_);
lean_ctor_set(v___x_2741_, 2, v___x_2740_);
lean_ctor_set_float(v___x_2741_, sizeof(void*)*3, v___x_2738_);
lean_ctor_set_float(v___x_2741_, sizeof(void*)*3 + 8, v___x_2738_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*3 + 16, v___x_2739_);
v___x_2742_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2743_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v_a_2713_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
lean_inc(v_ref_2711_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v_ref_2711_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_PersistentArray_push___redArg(v_traces_2732_, v___x_2744_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2745_);
v___x_2747_ = v___x_2734_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2745_);
lean_ctor_set_uint64(v_reuseFailAlloc_2755_, sizeof(void*)*1, v_tid_2731_);
v___x_2747_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 4, v___x_2747_);
v___x_2749_ = v___x_2729_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_env_2719_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_nextMacroScope_2720_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_ngen_2721_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_auxDeclNGen_2722_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2754_, 5, v_cache_2723_);
lean_ctor_set(v_reuseFailAlloc_2754_, 6, v_recordedDeps_2724_);
lean_ctor_set(v_reuseFailAlloc_2754_, 7, v_messages_2725_);
lean_ctor_set(v_reuseFailAlloc_2754_, 8, v_infoState_2726_);
lean_ctor_set(v_reuseFailAlloc_2754_, 9, v_snapshotTasks_2727_);
v___x_2749_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_st_ref_put(v___y_2709_, v___x_2749_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2736_);
v___x_2752_ = v___x_2715_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2736_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2759_, v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2766_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2767_, lean_object* v_i_2768_, lean_object* v_k_2769_){
_start:
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = lean_array_get_size(v_keys_2767_);
v___x_2771_ = lean_nat_dec_lt(v_i_2768_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_dec(v_i_2768_);
return v___x_2771_;
}
else
{
lean_object* v_k_x27_2772_; uint8_t v___x_2773_; 
v_k_x27_2772_ = lean_array_fget_borrowed(v_keys_2767_, v_i_2768_);
v___x_2773_ = l_Lean_instBEqExtraModUse_beq(v_k_2769_, v_k_x27_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_add(v_i_2768_, v___x_2774_);
lean_dec(v_i_2768_);
v_i_2768_ = v___x_2775_;
goto _start;
}
else
{
lean_dec(v_i_2768_);
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2777_, lean_object* v_i_2778_, lean_object* v_k_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2777_, v_i_2778_, v_k_2779_);
lean_dec_ref(v_k_2779_);
lean_dec_ref(v_keys_2777_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2782_, size_t v_x_2783_, lean_object* v_x_2784_){
_start:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v_es_2785_; lean_object* v___x_2786_; size_t v___x_2787_; size_t v___x_2788_; lean_object* v_j_2789_; lean_object* v___x_2790_; 
v_es_2785_ = lean_ctor_get(v_x_2782_, 0);
v___x_2786_ = lean_box(2);
v___x_2787_ = ((size_t)31ULL);
v___x_2788_ = lean_usize_land(v_x_2783_, v___x_2787_);
v_j_2789_ = lean_usize_to_nat(v___x_2788_);
v___x_2790_ = lean_array_get_borrowed(v___x_2786_, v_es_2785_, v_j_2789_);
lean_dec(v_j_2789_);
switch(lean_obj_tag(v___x_2790_))
{
case 0:
{
lean_object* v_key_2791_; uint8_t v___x_2792_; 
v_key_2791_ = lean_ctor_get(v___x_2790_, 0);
v___x_2792_ = l_Lean_instBEqExtraModUse_beq(v_x_2784_, v_key_2791_);
return v___x_2792_;
}
case 1:
{
lean_object* v_node_2793_; size_t v___x_2794_; size_t v___x_2795_; 
v_node_2793_ = lean_ctor_get(v___x_2790_, 0);
v___x_2794_ = ((size_t)5ULL);
v___x_2795_ = lean_usize_shift_right(v_x_2783_, v___x_2794_);
v_x_2782_ = v_node_2793_;
v_x_2783_ = v___x_2795_;
goto _start;
}
default: 
{
uint8_t v___x_2797_; 
v___x_2797_ = 0;
return v___x_2797_;
}
}
}
else
{
lean_object* v_ks_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v_ks_2798_ = lean_ctor_get(v_x_2782_, 0);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2798_, v___x_2799_, v_x_2784_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_){
_start:
{
size_t v_x_15804__boxed_2804_; uint8_t v_res_2805_; lean_object* v_r_2806_; 
v_x_15804__boxed_2804_ = lean_unbox_usize(v_x_2802_);
lean_dec(v_x_2802_);
v_res_2805_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2801_, v_x_15804__boxed_2804_, v_x_2803_);
lean_dec_ref(v_x_2803_);
lean_dec_ref(v_x_2801_);
v_r_2806_ = lean_box(v_res_2805_);
return v_r_2806_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
uint64_t v___x_2809_; size_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2809_ = l_Lean_instHashableExtraModUse_hash(v_x_2808_);
v___x_2810_ = lean_uint64_to_usize(v___x_2809_);
v___x_2811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2807_, v___x_2810_, v_x_2808_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
uint8_t v_res_2814_; lean_object* v_r_2815_; 
v_res_2814_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2812_, v_x_2813_);
lean_dec_ref(v_x_2813_);
lean_dec_ref(v_x_2812_);
v_r_2815_ = lean_box(v_res_2814_);
return v_r_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0(lean_object* v___x_2816_, lean_object* v_entry_2817_, lean_object* v_s_2818_){
_start:
{
lean_object* v_addEntryFn_2819_; lean_object* v_importedEntries_2820_; lean_object* v_state_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2829_; 
v_addEntryFn_2819_ = lean_ctor_get(v___x_2816_, 3);
lean_inc(v_addEntryFn_2819_);
lean_dec_ref(v___x_2816_);
v_importedEntries_2820_ = lean_ctor_get(v_s_2818_, 0);
v_state_2821_ = lean_ctor_get(v_s_2818_, 1);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_s_2818_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2823_ = v_s_2818_;
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_state_2821_);
lean_inc(v_importedEntries_2820_);
lean_dec(v_s_2818_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_state_2825_; lean_object* v___x_2827_; 
v_state_2825_ = lean_apply_2(v_addEntryFn_2819_, v_state_2821_, v_entry_2817_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_state_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_importedEntries_2820_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_state_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2830_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
return v___x_2839_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_cls_2845_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2846_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9));
v___x_2847_ = l_Lean_Name_append(v___x_2846_, v_cls_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2850_ = l_Lean_stringToMessageData(v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2853_ = l_Lean_stringToMessageData(v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2858_, uint8_t v_isMeta_2859_, lean_object* v_hint_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_env_2900_; uint8_t v_isExporting_2901_; lean_object* v_entry_2902_; lean_object* v___x_2903_; lean_object* v_env_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2898_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_2899_ = lean_st_ref_get(v___y_2864_);
v_env_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc_ref(v_env_2900_);
lean_dec(v___x_2899_);
v_isExporting_2901_ = lean_ctor_get_uint8(v_env_2900_, sizeof(void*)*13);
lean_dec_ref(v_env_2900_);
lean_inc(v_mod_2858_);
v_entry_2902_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2902_, 0, v_mod_2858_);
lean_ctor_set_uint8(v_entry_2902_, sizeof(void*)*1, v_isExporting_2901_);
lean_ctor_set_uint8(v_entry_2902_, sizeof(void*)*1 + 1, v_isMeta_2859_);
v___x_2903_ = lean_st_ref_get(v___y_2864_);
v_env_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc_ref(v_env_2904_);
lean_dec(v___x_2903_);
v___x_2905_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2906_ = lean_box(1);
v___x_2907_ = lean_box(0);
v___x_2908_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2898_, v___x_2905_, v_env_2904_, v___x_2906_, v___x_2907_);
v___x_2909_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2908_, v_entry_2902_);
lean_dec(v___x_2908_);
if (v___x_2909_ == 0)
{
lean_object* v_toCold_2910_; lean_object* v_options_2911_; lean_object* v_inheritedTraceOptions_2912_; uint8_t v_hasTrace_2913_; lean_object* v___f_2914_; uint8_t v___x_2915_; lean_object* v___y_2917_; lean_object* v___y_2918_; 
v_toCold_2910_ = lean_ctor_get(v___y_2863_, 0);
v_options_2911_ = lean_ctor_get(v_toCold_2910_, 2);
v_inheritedTraceOptions_2912_ = lean_ctor_get(v_toCold_2910_, 11);
v_hasTrace_2913_ = lean_ctor_get_uint8(v_options_2911_, sizeof(void*)*1);
v___f_2914_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2914_, 0, v___x_2905_);
lean_closure_set(v___f_2914_, 1, v_entry_2902_);
v___x_2915_ = 1;
if (v_hasTrace_2913_ == 0)
{
lean_dec(v_hint_2860_);
lean_dec(v_mod_2858_);
v___y_2917_ = v___y_2862_;
v___y_2918_ = v___y_2864_;
goto v___jp_2916_;
}
else
{
lean_object* v_cls_2945_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_cls_2945_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2965_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_2966_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2912_, v_options_2911_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec(v_hint_2860_);
lean_dec(v_mod_2858_);
v___y_2917_ = v___y_2862_;
v___y_2918_ = v___y_2864_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2967_; lean_object* v___y_2969_; 
v___x_2967_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_2901_ == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2969_ = v___x_2976_;
goto v___jp_2968_;
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2969_ = v___x_2977_;
goto v___jp_2968_;
}
v___jp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_inc_ref(v___y_2969_);
v___x_2970_ = l_Lean_stringToMessageData(v___y_2969_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2967_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
if (v_isMeta_2859_ == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_2952_ = v___x_2973_;
v___y_2953_ = v___x_2974_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_2952_ = v___x_2973_;
v___y_2953_ = v___x_2975_;
goto v___jp_2951_;
}
}
}
v___jp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___y_2947_);
lean_ctor_set(v___x_2949_, 1, v___y_2948_);
v___x_2950_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2945_, v___x_2949_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_dec_ref_known(v___x_2950_, 1);
v___y_2917_ = v___y_2862_;
v___y_2918_ = v___y_2864_;
goto v___jp_2916_;
}
else
{
lean_dec_ref(v___f_2914_);
return v___x_2950_;
}
}
v___jp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
lean_inc_ref(v___y_2953_);
v___x_2954_ = l_Lean_stringToMessageData(v___y_2953_);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___y_2952_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_MessageData_ofName(v_mod_2858_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_Name_isAnonymous(v_hint_2860_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2962_ = l_Lean_MessageData_ofName(v_hint_2860_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___y_2947_ = v___x_2959_;
v___y_2948_ = v___x_2963_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2964_; 
lean_dec(v_hint_2860_);
v___x_2964_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_2947_ = v___x_2959_;
v___y_2948_ = v___x_2964_;
goto v___jp_2946_;
}
}
}
v___jp_2916_:
{
lean_object* v___x_2919_; lean_object* v_toEnvExtension_2920_; uint8_t v_logWrites_2921_; 
v___x_2919_ = lean_st_ref_take(v___y_2918_);
v_toEnvExtension_2920_ = lean_ctor_get(v___x_2905_, 0);
v_logWrites_2921_ = lean_ctor_get_uint8(v_toEnvExtension_2920_, sizeof(void*)*6);
if (v_logWrites_2921_ == 0)
{
lean_object* v_env_2922_; lean_object* v_nextMacroScope_2923_; lean_object* v_ngen_2924_; lean_object* v_auxDeclNGen_2925_; lean_object* v_traceState_2926_; lean_object* v_recordedDeps_2927_; lean_object* v_messages_2928_; lean_object* v_infoState_2929_; lean_object* v_snapshotTasks_2930_; lean_object* v_asyncMode_2931_; lean_object* v___x_2932_; 
v_env_2922_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2922_);
v_nextMacroScope_2923_ = lean_ctor_get(v___x_2919_, 1);
lean_inc(v_nextMacroScope_2923_);
v_ngen_2924_ = lean_ctor_get(v___x_2919_, 2);
lean_inc_ref(v_ngen_2924_);
v_auxDeclNGen_2925_ = lean_ctor_get(v___x_2919_, 3);
lean_inc_ref(v_auxDeclNGen_2925_);
v_traceState_2926_ = lean_ctor_get(v___x_2919_, 4);
lean_inc_ref(v_traceState_2926_);
v_recordedDeps_2927_ = lean_ctor_get(v___x_2919_, 6);
lean_inc_ref(v_recordedDeps_2927_);
v_messages_2928_ = lean_ctor_get(v___x_2919_, 7);
lean_inc_ref(v_messages_2928_);
v_infoState_2929_ = lean_ctor_get(v___x_2919_, 8);
lean_inc_ref(v_infoState_2929_);
v_snapshotTasks_2930_ = lean_ctor_get(v___x_2919_, 9);
lean_inc_ref(v_snapshotTasks_2930_);
lean_dec(v___x_2919_);
v_asyncMode_2931_ = lean_ctor_get(v_toEnvExtension_2920_, 2);
lean_inc_ref(v_toEnvExtension_2920_);
v___x_2932_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2920_, v_env_2922_, v___f_2914_, v_asyncMode_2931_, v___x_2907_, v___x_2915_);
v___y_2867_ = v_infoState_2929_;
v___y_2868_ = v_snapshotTasks_2930_;
v___y_2869_ = v___y_2918_;
v___y_2870_ = v_messages_2928_;
v___y_2871_ = v_traceState_2926_;
v___y_2872_ = v_nextMacroScope_2923_;
v___y_2873_ = v___y_2917_;
v___y_2874_ = v_auxDeclNGen_2925_;
v___y_2875_ = v_recordedDeps_2927_;
v___y_2876_ = v_ngen_2924_;
v___y_2877_ = v___x_2932_;
goto v___jp_2866_;
}
else
{
lean_object* v_env_2933_; lean_object* v_nextMacroScope_2934_; lean_object* v_ngen_2935_; lean_object* v_auxDeclNGen_2936_; lean_object* v_traceState_2937_; lean_object* v_recordedDeps_2938_; lean_object* v_messages_2939_; lean_object* v_infoState_2940_; lean_object* v_snapshotTasks_2941_; lean_object* v_asyncMode_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_env_2933_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2933_);
v_nextMacroScope_2934_ = lean_ctor_get(v___x_2919_, 1);
lean_inc(v_nextMacroScope_2934_);
v_ngen_2935_ = lean_ctor_get(v___x_2919_, 2);
lean_inc_ref(v_ngen_2935_);
v_auxDeclNGen_2936_ = lean_ctor_get(v___x_2919_, 3);
lean_inc_ref(v_auxDeclNGen_2936_);
v_traceState_2937_ = lean_ctor_get(v___x_2919_, 4);
lean_inc_ref(v_traceState_2937_);
v_recordedDeps_2938_ = lean_ctor_get(v___x_2919_, 6);
lean_inc_ref(v_recordedDeps_2938_);
v_messages_2939_ = lean_ctor_get(v___x_2919_, 7);
lean_inc_ref(v_messages_2939_);
v_infoState_2940_ = lean_ctor_get(v___x_2919_, 8);
lean_inc_ref(v_infoState_2940_);
v_snapshotTasks_2941_ = lean_ctor_get(v___x_2919_, 9);
lean_inc_ref(v_snapshotTasks_2941_);
lean_dec(v___x_2919_);
v_asyncMode_2942_ = lean_ctor_get(v_toEnvExtension_2920_, 2);
lean_inc_ref_n(v_toEnvExtension_2920_, 2);
v___x_2943_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2920_, v_env_2933_);
lean_dec_ref(v_env_2933_);
v___x_2944_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2920_, v___x_2943_, v___f_2914_, v_asyncMode_2942_, v___x_2907_, v___x_2915_);
v___y_2867_ = v_infoState_2940_;
v___y_2868_ = v_snapshotTasks_2941_;
v___y_2869_ = v___y_2918_;
v___y_2870_ = v_messages_2939_;
v___y_2871_ = v_traceState_2937_;
v___y_2872_ = v_nextMacroScope_2934_;
v___y_2873_ = v___y_2917_;
v___y_2874_ = v_auxDeclNGen_2936_;
v___y_2875_ = v_recordedDeps_2938_;
v___y_2876_ = v_ngen_2935_;
v___y_2877_ = v___x_2944_;
goto v___jp_2866_;
}
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref_known(v_entry_2902_, 1);
lean_dec(v_hint_2860_);
lean_dec(v_mod_2858_);
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
v___jp_2866_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_mctx_2882_; lean_object* v_zetaDeltaFVarIds_2883_; lean_object* v_postponed_2884_; lean_object* v_diag_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2896_; 
v___x_2878_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_2879_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2879_, 0, v___y_2877_);
lean_ctor_set(v___x_2879_, 1, v___y_2872_);
lean_ctor_set(v___x_2879_, 2, v___y_2876_);
lean_ctor_set(v___x_2879_, 3, v___y_2874_);
lean_ctor_set(v___x_2879_, 4, v___y_2871_);
lean_ctor_set(v___x_2879_, 5, v___x_2878_);
lean_ctor_set(v___x_2879_, 6, v___y_2875_);
lean_ctor_set(v___x_2879_, 7, v___y_2870_);
lean_ctor_set(v___x_2879_, 8, v___y_2867_);
lean_ctor_set(v___x_2879_, 9, v___y_2868_);
v___x_2880_ = lean_st_ref_put(v___y_2869_, v___x_2879_);
v___x_2881_ = lean_st_ref_take(v___y_2873_);
v_mctx_2882_ = lean_ctor_get(v___x_2881_, 0);
v_zetaDeltaFVarIds_2883_ = lean_ctor_get(v___x_2881_, 2);
v_postponed_2884_ = lean_ctor_get(v___x_2881_, 3);
v_diag_2885_ = lean_ctor_get(v___x_2881_, 4);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2881_, 1);
lean_dec(v_unused_2897_);
v___x_2887_ = v___x_2881_;
v_isShared_2888_ = v_isSharedCheck_2896_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_diag_2885_);
lean_inc(v_postponed_2884_);
lean_inc(v_zetaDeltaFVarIds_2883_);
lean_inc(v_mctx_2882_);
lean_dec(v___x_2881_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2896_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2889_ = lean_box(0);
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v___x_2890_);
v___x_2892_ = v___x_2887_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_mctx_2882_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_zetaDeltaFVarIds_2883_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_postponed_2884_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_diag_2885_);
v___x_2892_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_st_ref_put(v___y_2873_, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2889_);
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2980_, lean_object* v_isMeta_2981_, lean_object* v_hint_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v_isMeta_boxed_2988_; lean_object* v_res_2989_; 
v_isMeta_boxed_2988_ = lean_unbox(v_isMeta_2981_);
v_res_2989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2980_, v_isMeta_boxed_2988_, v_hint_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2990_, lean_object* v_x_2991_){
_start:
{
if (lean_obj_tag(v_x_2991_) == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_box(0);
return v___x_2992_;
}
else
{
lean_object* v_key_2993_; lean_object* v_value_2994_; lean_object* v_tail_2995_; uint8_t v___x_2996_; 
v_key_2993_ = lean_ctor_get(v_x_2991_, 0);
v_value_2994_ = lean_ctor_get(v_x_2991_, 1);
v_tail_2995_ = lean_ctor_get(v_x_2991_, 2);
v___x_2996_ = lean_name_eq(v_key_2993_, v_a_2990_);
if (v___x_2996_ == 0)
{
v_x_2991_ = v_tail_2995_;
goto _start;
}
else
{
lean_object* v___x_2998_; 
lean_inc(v_value_2994_);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_value_2994_);
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2999_, v_x_3000_);
lean_dec(v_x_3000_);
lean_dec(v_a_2999_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_buckets_3004_; lean_object* v___x_3005_; uint64_t v___y_3007_; 
v_buckets_3004_ = lean_ctor_get(v_m_3002_, 1);
v___x_3005_ = lean_array_get_size(v_buckets_3004_);
if (lean_obj_tag(v_a_3003_) == 0)
{
uint64_t v___x_3021_; 
v___x_3021_ = 1723ULL;
v___y_3007_ = v___x_3021_;
goto v___jp_3006_;
}
else
{
uint64_t v_hash_3022_; 
v_hash_3022_ = lean_ctor_get_uint64(v_a_3003_, sizeof(void*)*2);
v___y_3007_ = v_hash_3022_;
goto v___jp_3006_;
}
v___jp_3006_:
{
uint64_t v___x_3008_; uint64_t v___x_3009_; uint64_t v_fold_3010_; uint64_t v___x_3011_; uint64_t v___x_3012_; uint64_t v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3008_ = 32ULL;
v___x_3009_ = lean_uint64_shift_right(v___y_3007_, v___x_3008_);
v_fold_3010_ = lean_uint64_xor(v___y_3007_, v___x_3009_);
v___x_3011_ = 16ULL;
v___x_3012_ = lean_uint64_shift_right(v_fold_3010_, v___x_3011_);
v___x_3013_ = lean_uint64_xor(v_fold_3010_, v___x_3012_);
v___x_3014_ = lean_uint64_to_usize(v___x_3013_);
v___x_3015_ = lean_usize_of_nat(v___x_3005_);
v___x_3016_ = ((size_t)1ULL);
v___x_3017_ = lean_usize_sub(v___x_3015_, v___x_3016_);
v___x_3018_ = lean_usize_land(v___x_3014_, v___x_3017_);
v___x_3019_ = lean_array_uget_borrowed(v_buckets_3004_, v___x_3018_);
v___x_3020_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3003_, v___x_3019_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_m_3023_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_3026_, lean_object* v_declName_3027_, lean_object* v_as_3028_, size_t v_sz_3029_, size_t v_i_3030_, lean_object* v_b_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_usize_dec_lt(v_i_3030_, v_sz_3029_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
lean_dec(v_declName_3027_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_b_3031_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; lean_object* v_modules_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v_toImport_3044_; lean_object* v_module_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3039_ = l_Lean_Environment_header(v___x_3026_);
v_modules_3040_ = lean_ctor_get(v___x_3039_, 3);
lean_inc_ref(v_modules_3040_);
lean_dec_ref(v___x_3039_);
v___x_3041_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3042_ = lean_array_uget_borrowed(v_as_3028_, v_i_3030_);
v___x_3043_ = lean_array_get(v___x_3041_, v_modules_3040_, v_a_3042_);
lean_dec_ref(v_modules_3040_);
v_toImport_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc_ref(v_toImport_3044_);
lean_dec(v___x_3043_);
v_module_3045_ = lean_ctor_get(v_toImport_3044_, 0);
lean_inc(v_module_3045_);
lean_dec_ref(v_toImport_3044_);
v___x_3046_ = lean_box(0);
v___x_3047_ = 0;
lean_inc(v_declName_3027_);
v___x_3048_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3045_, v___x_3047_, v_declName_3027_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
if (lean_obj_tag(v___x_3048_) == 0)
{
size_t v___x_3049_; size_t v___x_3050_; 
lean_dec_ref_known(v___x_3048_, 1);
v___x_3049_ = ((size_t)1ULL);
v___x_3050_ = lean_usize_add(v_i_3030_, v___x_3049_);
v_i_3030_ = v___x_3050_;
v_b_3031_ = v___x_3046_;
goto _start;
}
else
{
lean_dec(v_declName_3027_);
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3052_, lean_object* v_declName_3053_, lean_object* v_as_3054_, lean_object* v_sz_3055_, lean_object* v_i_3056_, lean_object* v_b_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3055_);
lean_dec(v_sz_3055_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3056_);
lean_dec(v_i_3056_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3052_, v_declName_3053_, v_as_3054_, v_sz_boxed_3063_, v_i_boxed_3064_, v_b_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_as_3054_);
lean_dec_ref(v___x_3052_);
return v_res_3065_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3069_, uint8_t v_isMeta_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v_env_3081_; lean_object* v___y_3083_; lean_object* v___x_3096_; 
v___x_3076_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3077_ = lean_st_ref_get(v___y_3074_);
v_env_3081_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3081_);
lean_dec(v___x_3077_);
v___x_3096_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3081_, v_declName_3069_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3069_);
goto v___jp_3078_;
}
else
{
lean_object* v_val_3097_; lean_object* v___x_3098_; lean_object* v_modules_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_val_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_Environment_header(v_env_3081_);
v_modules_3099_ = lean_ctor_get(v___x_3098_, 3);
lean_inc_ref(v_modules_3099_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = lean_array_get_size(v_modules_3099_);
v___x_3101_ = lean_nat_dec_lt(v_val_3097_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec_ref(v_modules_3099_);
lean_dec(v_val_3097_);
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3069_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___y_3105_; 
v___x_3102_ = lean_array_fget(v_modules_3099_, v_val_3097_);
lean_dec(v_val_3097_);
lean_dec_ref(v_modules_3099_);
v___x_3103_ = lean_st_ref_get(v___y_3074_);
if (v_isMeta_3070_ == 0)
{
lean_dec(v___x_3103_);
v___y_3105_ = v_isMeta_3070_;
goto v___jp_3104_;
}
else
{
lean_object* v_env_3116_; uint8_t v___x_3117_; 
v_env_3116_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_env_3116_);
lean_dec(v___x_3103_);
lean_inc(v_declName_3069_);
v___x_3117_ = l_Lean_isMarkedMeta(v_env_3116_, v_declName_3069_);
if (v___x_3117_ == 0)
{
v___y_3105_ = v_isMeta_3070_;
goto v___jp_3104_;
}
else
{
uint8_t v___x_3118_; 
v___x_3118_ = 0;
v___y_3105_ = v___x_3118_;
goto v___jp_3104_;
}
}
v___jp_3104_:
{
lean_object* v_toImport_3106_; lean_object* v_module_3107_; lean_object* v___x_3108_; 
v_toImport_3106_ = lean_ctor_get(v___x_3102_, 0);
lean_inc_ref(v_toImport_3106_);
lean_dec(v___x_3102_);
v_module_3107_ = lean_ctor_get(v_toImport_3106_, 0);
lean_inc(v_module_3107_);
lean_dec_ref(v_toImport_3106_);
lean_inc(v_declName_3069_);
v___x_3108_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3107_, v___y_3105_, v_declName_3069_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref_known(v___x_3108_, 1);
v___x_3109_ = l_Lean_indirectModUseExt;
v___x_3110_ = lean_box(1);
v___x_3111_ = lean_box(0);
lean_inc_ref(v_env_3081_);
v___x_3112_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3076_, v___x_3109_, v_env_3081_, v___x_3110_, v___x_3111_);
v___x_3113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3112_, v_declName_3069_);
lean_dec(v___x_3112_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3083_ = v___x_3114_;
goto v___jp_3082_;
}
else
{
lean_object* v_val_3115_; 
v_val_3115_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v___x_3113_, 1);
v___y_3083_ = v_val_3115_;
goto v___jp_3082_;
}
}
else
{
lean_dec_ref(v_env_3081_);
lean_dec(v_declName_3069_);
return v___x_3108_;
}
}
}
}
v___jp_3078_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
v___jp_3082_:
{
lean_object* v___x_3084_; size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3084_ = lean_box(0);
v_sz_3085_ = lean_array_size(v___y_3083_);
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3081_, v_declName_3069_, v___y_3083_, v_sz_3085_, v___x_3086_, v___x_3084_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_env_3081_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3095_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3084_);
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3084_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3119_, lean_object* v_isMeta_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v_isMeta_boxed_3126_; lean_object* v_res_3127_; 
v_isMeta_boxed_3126_ = lean_unbox(v_isMeta_3120_);
v_res_3127_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3119_, v_isMeta_boxed_3126_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3128_, uint8_t v_isExporting_3129_, lean_object* v___x_3130_, lean_object* v___y_3131_, lean_object* v___x_3132_, lean_object* v_a_x3f_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v_env_3136_; lean_object* v_nextMacroScope_3137_; lean_object* v_ngen_3138_; lean_object* v_auxDeclNGen_3139_; lean_object* v_traceState_3140_; lean_object* v_recordedDeps_3141_; lean_object* v_messages_3142_; lean_object* v_infoState_3143_; lean_object* v_snapshotTasks_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3169_; 
v___x_3135_ = lean_st_ref_take(v___y_3128_);
v_env_3136_ = lean_ctor_get(v___x_3135_, 0);
v_nextMacroScope_3137_ = lean_ctor_get(v___x_3135_, 1);
v_ngen_3138_ = lean_ctor_get(v___x_3135_, 2);
v_auxDeclNGen_3139_ = lean_ctor_get(v___x_3135_, 3);
v_traceState_3140_ = lean_ctor_get(v___x_3135_, 4);
v_recordedDeps_3141_ = lean_ctor_get(v___x_3135_, 6);
v_messages_3142_ = lean_ctor_get(v___x_3135_, 7);
v_infoState_3143_ = lean_ctor_get(v___x_3135_, 8);
v_snapshotTasks_3144_ = lean_ctor_get(v___x_3135_, 9);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v___x_3135_, 5);
lean_dec(v_unused_3170_);
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3169_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_snapshotTasks_3144_);
lean_inc(v_infoState_3143_);
lean_inc(v_messages_3142_);
lean_inc(v_recordedDeps_3141_);
lean_inc(v_traceState_3140_);
lean_inc(v_auxDeclNGen_3139_);
lean_inc(v_ngen_3138_);
lean_inc(v_nextMacroScope_3137_);
lean_inc(v_env_3136_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3169_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = l_Lean_Environment_setExporting(v_env_3136_, v_isExporting_3129_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 5, v___x_3130_);
lean_ctor_set(v___x_3146_, 0, v___x_3148_);
v___x_3150_ = v___x_3146_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_nextMacroScope_3137_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_ngen_3138_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_auxDeclNGen_3139_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v_traceState_3140_);
lean_ctor_set(v_reuseFailAlloc_3168_, 5, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3168_, 6, v_recordedDeps_3141_);
lean_ctor_set(v_reuseFailAlloc_3168_, 7, v_messages_3142_);
lean_ctor_set(v_reuseFailAlloc_3168_, 8, v_infoState_3143_);
lean_ctor_set(v_reuseFailAlloc_3168_, 9, v_snapshotTasks_3144_);
v___x_3150_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_mctx_3153_; lean_object* v_zetaDeltaFVarIds_3154_; lean_object* v_postponed_3155_; lean_object* v_diag_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3166_; 
v___x_3151_ = lean_st_ref_put(v___y_3128_, v___x_3150_);
v___x_3152_ = lean_st_ref_take(v___y_3131_);
v_mctx_3153_ = lean_ctor_get(v___x_3152_, 0);
v_zetaDeltaFVarIds_3154_ = lean_ctor_get(v___x_3152_, 2);
v_postponed_3155_ = lean_ctor_get(v___x_3152_, 3);
v_diag_3156_ = lean_ctor_get(v___x_3152_, 4);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3152_, 1);
lean_dec(v_unused_3167_);
v___x_3158_ = v___x_3152_;
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_diag_3156_);
lean_inc(v_postponed_3155_);
lean_inc(v_zetaDeltaFVarIds_3154_);
lean_inc(v_mctx_3153_);
lean_dec(v___x_3152_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_box(0);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 1, v___x_3132_);
v___x_3162_ = v___x_3158_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_mctx_3153_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_zetaDeltaFVarIds_3154_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_postponed_3155_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_diag_3156_);
v___x_3162_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_st_ref_put(v___y_3131_, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3160_);
return v___x_3164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3171_, lean_object* v_isExporting_3172_, lean_object* v___x_3173_, lean_object* v___y_3174_, lean_object* v___x_3175_, lean_object* v_a_x3f_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v_isExporting_boxed_3178_; lean_object* v_res_3179_; 
v_isExporting_boxed_3178_ = lean_unbox(v_isExporting_3172_);
v_res_3179_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3171_, v_isExporting_boxed_3178_, v___x_3173_, v___y_3174_, v___x_3175_, v_a_x3f_3176_);
lean_dec(v_a_x3f_3176_);
lean_dec(v___y_3174_);
lean_dec(v___y_3171_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3180_, uint8_t v_isExporting_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v_env_3188_; lean_object* v___x_3189_; uint8_t v_isModule_3190_; 
v___x_3187_ = lean_st_ref_get(v___y_3185_);
v_env_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_ref(v_env_3188_);
lean_dec(v___x_3187_);
v___x_3189_ = l_Lean_Environment_header(v_env_3188_);
v_isModule_3190_ = lean_ctor_get_uint8(v___x_3189_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3189_);
if (v_isModule_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref(v_env_3188_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v___x_3191_ = lean_apply_5(v_x_3180_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, lean_box(0));
return v___x_3191_;
}
else
{
uint8_t v_isExporting_3192_; 
v_isExporting_3192_ = lean_ctor_get_uint8(v_env_3188_, sizeof(void*)*13);
lean_dec_ref(v_env_3188_);
if (v_isExporting_3181_ == 0)
{
if (v_isExporting_3192_ == 0)
{
lean_object* v___x_3259_; 
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v___x_3259_ = lean_apply_5(v_x_3180_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, lean_box(0));
return v___x_3259_;
}
else
{
goto v___jp_3193_;
}
}
else
{
if (v_isExporting_3192_ == 0)
{
goto v___jp_3193_;
}
else
{
lean_object* v___x_3260_; 
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v___x_3260_ = lean_apply_5(v_x_3180_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, lean_box(0));
return v___x_3260_;
}
}
v___jp_3193_:
{
lean_object* v___x_3194_; lean_object* v_env_3195_; lean_object* v_nextMacroScope_3196_; lean_object* v_ngen_3197_; lean_object* v_auxDeclNGen_3198_; lean_object* v_traceState_3199_; lean_object* v_recordedDeps_3200_; lean_object* v_messages_3201_; lean_object* v_infoState_3202_; lean_object* v_snapshotTasks_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3257_; 
v___x_3194_ = lean_st_ref_take(v___y_3185_);
v_env_3195_ = lean_ctor_get(v___x_3194_, 0);
v_nextMacroScope_3196_ = lean_ctor_get(v___x_3194_, 1);
v_ngen_3197_ = lean_ctor_get(v___x_3194_, 2);
v_auxDeclNGen_3198_ = lean_ctor_get(v___x_3194_, 3);
v_traceState_3199_ = lean_ctor_get(v___x_3194_, 4);
v_recordedDeps_3200_ = lean_ctor_get(v___x_3194_, 6);
v_messages_3201_ = lean_ctor_get(v___x_3194_, 7);
v_infoState_3202_ = lean_ctor_get(v___x_3194_, 8);
v_snapshotTasks_3203_ = lean_ctor_get(v___x_3194_, 9);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v___x_3194_, 5);
lean_dec(v_unused_3258_);
v___x_3205_ = v___x_3194_;
v_isShared_3206_ = v_isSharedCheck_3257_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_snapshotTasks_3203_);
lean_inc(v_infoState_3202_);
lean_inc(v_messages_3201_);
lean_inc(v_recordedDeps_3200_);
lean_inc(v_traceState_3199_);
lean_inc(v_auxDeclNGen_3198_);
lean_inc(v_ngen_3197_);
lean_inc(v_nextMacroScope_3196_);
lean_inc(v_env_3195_);
lean_dec(v___x_3194_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3257_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3207_ = l_Lean_Environment_setExporting(v_env_3195_, v_isExporting_3181_);
v___x_3208_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 5, v___x_3208_);
lean_ctor_set(v___x_3205_, 0, v___x_3207_);
v___x_3210_ = v___x_3205_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_nextMacroScope_3196_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_ngen_3197_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_auxDeclNGen_3198_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_traceState_3199_);
lean_ctor_set(v_reuseFailAlloc_3256_, 5, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3256_, 6, v_recordedDeps_3200_);
lean_ctor_set(v_reuseFailAlloc_3256_, 7, v_messages_3201_);
lean_ctor_set(v_reuseFailAlloc_3256_, 8, v_infoState_3202_);
lean_ctor_set(v_reuseFailAlloc_3256_, 9, v_snapshotTasks_3203_);
v___x_3210_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_mctx_3213_; lean_object* v_zetaDeltaFVarIds_3214_; lean_object* v_postponed_3215_; lean_object* v_diag_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3254_; 
v___x_3211_ = lean_st_ref_put(v___y_3185_, v___x_3210_);
v___x_3212_ = lean_st_ref_take(v___y_3183_);
v_mctx_3213_ = lean_ctor_get(v___x_3212_, 0);
v_zetaDeltaFVarIds_3214_ = lean_ctor_get(v___x_3212_, 2);
v_postponed_3215_ = lean_ctor_get(v___x_3212_, 3);
v_diag_3216_ = lean_ctor_get(v___x_3212_, 4);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v___x_3212_, 1);
lean_dec(v_unused_3255_);
v___x_3218_ = v___x_3212_;
v_isShared_3219_ = v_isSharedCheck_3254_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_diag_3216_);
lean_inc(v_postponed_3215_);
lean_inc(v_zetaDeltaFVarIds_3214_);
lean_inc(v_mctx_3213_);
lean_dec(v___x_3212_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3254_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_mctx_3213_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_zetaDeltaFVarIds_3214_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v_postponed_3215_);
lean_ctor_set(v_reuseFailAlloc_3253_, 4, v_diag_3216_);
v___x_3222_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v_r_3224_; 
v___x_3223_ = lean_st_ref_put(v___y_3183_, v___x_3222_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v_r_3224_ = lean_apply_5(v_x_3180_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, lean_box(0));
if (lean_obj_tag(v_r_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3241_; 
v_a_3225_ = lean_ctor_get(v_r_3224_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_r_3224_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3227_ = v_r_3224_;
v_isShared_3228_ = v_isSharedCheck_3241_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v_r_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3241_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
lean_inc(v_a_3225_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 1);
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v___x_3231_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3185_, v_isExporting_3192_, v___x_3208_, v___y_3183_, v___x_3220_, v___x_3230_);
lean_dec_ref(v___x_3230_);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3231_, 0);
lean_dec(v_unused_3239_);
v___x_3233_ = v___x_3231_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3231_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v_a_3225_);
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3225_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v_a_3242_ = lean_ctor_get(v_r_3224_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v_r_3224_, 1);
v___x_3243_ = lean_box(0);
v___x_3244_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3185_, v_isExporting_3192_, v___x_3208_, v___y_3183_, v___x_3220_, v___x_3243_);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3244_, 0);
lean_dec(v_unused_3252_);
v___x_3246_ = v___x_3244_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3244_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 1);
lean_ctor_set(v___x_3246_, 0, v_a_3242_);
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3242_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3261_, lean_object* v_isExporting_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_isExporting_boxed_3268_; lean_object* v_res_3269_; 
v_isExporting_boxed_3268_ = lean_unbox(v_isExporting_3262_);
v_res_3269_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3261_, v_isExporting_boxed_3268_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3270_, uint8_t v_when_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
if (v_when_3271_ == 0)
{
lean_object* v___x_3277_; 
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
v___x_3277_ = lean_apply_5(v_x_3270_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, lean_box(0));
return v___x_3277_;
}
else
{
uint8_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = 0;
v___x_3279_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3270_, v___x_3278_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3280_, lean_object* v_when_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_when_boxed_3287_; lean_object* v_res_3288_; 
v_when_boxed_3287_ = lean_unbox(v_when_3281_);
v_res_3288_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3280_, v_when_boxed_3287_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_3289_, uint8_t v_showInfo_3290_, uint8_t v_minIndexable_3291_, lean_object* v_attrName_3292_, lean_object* v___x_3293_, lean_object* v_declName_3294_, lean_object* v_stx_3295_, uint8_t v_attrKind_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___f_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___y_3322_; lean_object* v___x_3332_; 
v___x_3300_ = 0;
v___x_3301_ = lean_box(v___x_3300_);
v___x_3302_ = lean_box(v_attrKind_3296_);
v___x_3303_ = lean_box(v_showInfo_3290_);
v___x_3304_ = lean_box(v_minIndexable_3291_);
lean_inc(v_declName_3294_);
v___f_3305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3305_, 0, v_declName_3294_);
lean_closure_set(v___f_3305_, 1, v___x_3301_);
lean_closure_set(v___f_3305_, 2, v___x_3302_);
lean_closure_set(v___f_3305_, 3, v_stx_3295_);
lean_closure_set(v___f_3305_, 4, v_ext_3289_);
lean_closure_set(v___f_3305_, 5, v___x_3303_);
lean_closure_set(v___f_3305_, 6, v___x_3304_);
lean_closure_set(v___f_3305_, 7, v_attrName_3292_);
v___x_3306_ = 1;
v___x_3307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3308_ = lean_unsigned_to_nat(32u);
v___x_3309_ = lean_mk_empty_array_with_capacity(v___x_3308_);
lean_dec_ref(v___x_3309_);
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3312_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3314_ = lean_box(0);
lean_inc(v___x_3293_);
v___x_3315_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3315_, 0, v___x_3307_);
lean_ctor_set(v___x_3315_, 1, v___x_3293_);
lean_ctor_set(v___x_3315_, 2, v___x_3312_);
lean_ctor_set(v___x_3315_, 3, v___x_3313_);
lean_ctor_set(v___x_3315_, 4, v___x_3314_);
lean_ctor_set(v___x_3315_, 5, v___x_3310_);
lean_ctor_set(v___x_3315_, 6, v___x_3314_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7, v___x_3300_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 1, v___x_3300_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 2, v___x_3300_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*7 + 3, v___x_3306_);
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
lean_ctor_set(v___x_3319_, 1, v___x_3317_);
lean_ctor_set(v___x_3319_, 2, v___x_3293_);
lean_ctor_set(v___x_3319_, 3, v___x_3311_);
lean_ctor_set(v___x_3319_, 4, v___x_3318_);
v___x_3320_ = lean_st_mk_ref(v___x_3319_);
v___x_3332_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3294_, v___x_3300_, v___x_3315_, v___x_3320_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3333_; 
lean_dec_ref_known(v___x_3332_, 1);
v___x_3333_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3305_, v___x_3306_, v___x_3315_, v___x_3320_, v___y_3297_, v___y_3298_);
lean_dec_ref_known(v___x_3315_, 7);
v___y_3322_ = v___x_3333_;
goto v___jp_3321_;
}
else
{
lean_dec_ref_known(v___x_3315_, 7);
lean_dec_ref(v___f_3305_);
v___y_3322_ = v___x_3332_;
goto v___jp_3321_;
}
v___jp_3321_:
{
if (lean_obj_tag(v___y_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3331_; 
v_a_3323_ = lean_ctor_get(v___y_3322_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___y_3322_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3325_ = v___y_3322_;
v_isShared_3326_ = v_isSharedCheck_3331_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___y_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3331_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3327_ = lean_st_ref_get(v___x_3320_);
lean_dec(v___x_3320_);
lean_dec(v___x_3327_);
if (v_isShared_3326_ == 0)
{
v___x_3329_ = v___x_3325_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
lean_dec(v___x_3320_);
return v___y_3322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_3334_, lean_object* v_showInfo_3335_, lean_object* v_minIndexable_3336_, lean_object* v_attrName_3337_, lean_object* v___x_3338_, lean_object* v_declName_3339_, lean_object* v_stx_3340_, lean_object* v_attrKind_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v_showInfo_boxed_3345_; uint8_t v_minIndexable_boxed_3346_; uint8_t v_attrKind_boxed_3347_; lean_object* v_res_3348_; 
v_showInfo_boxed_3345_ = lean_unbox(v_showInfo_3335_);
v_minIndexable_boxed_3346_ = lean_unbox(v_minIndexable_3336_);
v_attrKind_boxed_3347_ = lean_unbox(v_attrKind_3341_);
v_res_3348_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_3334_, v_showInfo_boxed_3345_, v_minIndexable_boxed_3346_, v_attrName_3337_, v___x_3338_, v_declName_3339_, v_stx_3340_, v_attrKind_boxed_3347_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3371_, uint8_t v_minIndexable_3372_, uint8_t v_showInfo_3373_, lean_object* v_ext_3374_, lean_object* v_ref_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___f_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___f_3382_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3428_; 
v___x_3377_ = lean_box(1);
v___x_3378_ = lean_box(v_showInfo_3373_);
lean_inc_n(v_attrName_3371_, 2);
lean_inc_ref(v_ext_3374_);
v___f_3379_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3379_, 0, v_ext_3374_);
lean_closure_set(v___f_3379_, 1, v___x_3377_);
lean_closure_set(v___f_3379_, 2, v___x_3378_);
lean_closure_set(v___f_3379_, 3, v_attrName_3371_);
v___x_3380_ = lean_box(v_showInfo_3373_);
v___x_3381_ = lean_box(v_minIndexable_3372_);
v___f_3382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3382_, 0, v_ext_3374_);
lean_closure_set(v___f_3382_, 1, v___x_3380_);
lean_closure_set(v___f_3382_, 2, v___x_3381_);
lean_closure_set(v___f_3382_, 3, v_attrName_3371_);
lean_closure_set(v___f_3382_, 4, v___x_3377_);
if (v_minIndexable_3372_ == 0)
{
if (v_showInfo_3373_ == 0)
{
lean_inc(v_attrName_3371_);
v___y_3428_ = v_attrName_3371_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3371_);
v___x_3457_ = lean_name_append_after(v_attrName_3371_, v___x_3456_);
v___y_3428_ = v___x_3457_;
goto v___jp_3427_;
}
}
else
{
if (v_showInfo_3373_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3371_);
v___x_3459_ = lean_name_append_after(v_attrName_3371_, v___x_3458_);
v___y_3428_ = v___x_3459_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3371_);
v___x_3461_ = lean_name_append_after(v_attrName_3371_, v___x_3460_);
v___y_3428_ = v___x_3461_;
goto v___jp_3427_;
}
}
v___jp_3383_:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3371_, v___x_3387_);
v___x_3389_ = lean_string_append(v___x_3386_, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_string_append(v___x_3391_, v___x_3388_);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3394_, v___x_3388_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
v___x_3398_ = lean_string_append(v___x_3397_, v___x_3388_);
v___x_3399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3400_ = lean_string_append(v___x_3398_, v___x_3399_);
v___x_3401_ = lean_string_append(v___x_3400_, v___x_3388_);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3403_ = lean_string_append(v___x_3401_, v___x_3402_);
v___x_3404_ = lean_string_append(v___x_3403_, v___x_3388_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3406_ = lean_string_append(v___x_3404_, v___x_3405_);
v___x_3407_ = lean_string_append(v___x_3406_, v___x_3388_);
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
v___x_3410_ = lean_string_append(v___x_3409_, v___x_3388_);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3412_ = lean_string_append(v___x_3410_, v___x_3411_);
v___x_3413_ = lean_string_append(v___x_3412_, v___x_3388_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3415_ = lean_string_append(v___x_3413_, v___x_3414_);
v___x_3416_ = lean_string_append(v___x_3415_, v___x_3388_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___x_3419_ = lean_string_append(v___x_3418_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3421_ = lean_string_append(v___x_3419_, v___x_3420_);
v___x_3422_ = lean_string_append(v___y_3385_, v___x_3421_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = 1;
v___x_3424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3424_, 0, v_ref_3375_);
lean_ctor_set(v___x_3424_, 1, v___y_3384_);
lean_ctor_set(v___x_3424_, 2, v___x_3422_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*3, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___f_3382_);
lean_ctor_set(v___x_3425_, 2, v___f_3379_);
v___x_3426_ = l_Lean_registerBuiltinAttribute(v___x_3425_);
return v___x_3426_;
}
v___jp_3427_:
{
if (v_minIndexable_3372_ == 0)
{
if (v_showInfo_3373_ == 0)
{
lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3430_ = 1;
lean_inc(v_attrName_3371_);
v___x_3431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3371_, v___x_3430_);
v___x_3432_ = lean_string_append(v___x_3429_, v___x_3431_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3434_ = lean_string_append(v___x_3432_, v___x_3433_);
v___y_3384_ = v___y_3428_;
v___y_3385_ = v___x_3434_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3371_);
v___x_3436_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3371_, v_showInfo_3373_);
v___x_3437_ = lean_string_append(v___x_3435_, v___x_3436_);
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3439_ = lean_string_append(v___x_3437_, v___x_3438_);
v___x_3440_ = lean_string_append(v___x_3439_, v___x_3436_);
lean_dec_ref(v___x_3436_);
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3442_ = lean_string_append(v___x_3440_, v___x_3441_);
v___y_3384_ = v___y_3428_;
v___y_3385_ = v___x_3442_;
goto v___jp_3383_;
}
}
else
{
if (v_showInfo_3373_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3371_);
v___x_3444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3371_, v_minIndexable_3372_);
v___x_3445_ = lean_string_append(v___x_3443_, v___x_3444_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3447_ = lean_string_append(v___x_3445_, v___x_3446_);
v___y_3384_ = v___y_3428_;
v___y_3385_ = v___x_3447_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3371_);
v___x_3449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3371_, v_showInfo_3373_);
v___x_3450_ = lean_string_append(v___x_3448_, v___x_3449_);
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3452_ = lean_string_append(v___x_3450_, v___x_3451_);
v___x_3453_ = lean_string_append(v___x_3452_, v___x_3449_);
lean_dec_ref(v___x_3449_);
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
v___y_3384_ = v___y_3428_;
v___y_3385_ = v___x_3455_;
goto v___jp_3383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3462_, lean_object* v_minIndexable_3463_, lean_object* v_showInfo_3464_, lean_object* v_ext_3465_, lean_object* v_ref_3466_, lean_object* v_a_3467_){
_start:
{
uint8_t v_minIndexable_boxed_3468_; uint8_t v_showInfo_boxed_3469_; lean_object* v_res_3470_; 
v_minIndexable_boxed_3468_ = lean_unbox(v_minIndexable_3463_);
v_showInfo_boxed_3469_ = lean_unbox(v_showInfo_3464_);
v_res_3470_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3462_, v_minIndexable_boxed_3468_, v_showInfo_boxed_3469_, v_ext_3465_, v_ref_3466_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3471_, lean_object* v_msg_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_msg_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3479_, v_msg_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3487_, uint8_t v_attrKind_3488_, uint8_t v_showInfo_3489_, uint8_t v_minIndexable_3490_, lean_object* v_as_3491_, lean_object* v_as_x27_3492_, lean_object* v_b_3493_, lean_object* v_a_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3487_, v_attrKind_3488_, v_showInfo_3489_, v_minIndexable_3490_, v_as_x27_3492_, v_b_3493_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3501_, lean_object* v_attrKind_3502_, lean_object* v_showInfo_3503_, lean_object* v_minIndexable_3504_, lean_object* v_as_3505_, lean_object* v_as_x27_3506_, lean_object* v_b_3507_, lean_object* v_a_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_attrKind_boxed_3514_; uint8_t v_showInfo_boxed_3515_; uint8_t v_minIndexable_boxed_3516_; lean_object* v_res_3517_; 
v_attrKind_boxed_3514_ = lean_unbox(v_attrKind_3502_);
v_showInfo_boxed_3515_ = lean_unbox(v_showInfo_3503_);
v_minIndexable_boxed_3516_ = lean_unbox(v_minIndexable_3504_);
v_res_3517_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3501_, v_attrKind_boxed_3514_, v_showInfo_boxed_3515_, v_minIndexable_boxed_3516_, v_as_3505_, v_as_x27_3506_, v_b_3507_, v_a_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_as_x27_3506_);
lean_dec(v_as_3505_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3518_, lean_object* v_x_3519_, uint8_t v_isExporting_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3519_, v_isExporting_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3527_, lean_object* v_x_3528_, lean_object* v_isExporting_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v_isExporting_boxed_3535_; lean_object* v_res_3536_; 
v_isExporting_boxed_3535_ = lean_unbox(v_isExporting_3529_);
v_res_3536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3527_, v_x_3528_, v_isExporting_boxed_3535_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3537_, lean_object* v_x_3538_, uint8_t v_when_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3538_, v_when_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_x_3547_, lean_object* v_when_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v_when_boxed_3554_; lean_object* v_res_3555_; 
v_when_boxed_3554_ = lean_unbox(v_when_3548_);
v_res_3555_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3546_, v_x_3547_, v_when_boxed_3554_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3556_, lean_object* v_m_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3557_, v_a_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3560_, lean_object* v_m_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3560_, v_m_3561_, v_a_3562_);
lean_dec(v_a_3562_);
lean_dec_ref(v_m_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v_res_3571_; lean_object* v_r_3572_; 
v_res_3571_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3568_, v_x_3569_, v_x_3570_);
lean_dec_ref(v_x_3570_);
lean_dec_ref(v_x_3569_);
v_r_3572_ = lean_box(v_res_3571_);
return v_r_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3573_, lean_object* v_a_3574_, lean_object* v_x_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3574_, v_x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3577_, lean_object* v_a_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3577_, v_a_3578_, v_x_3579_);
lean_dec(v_x_3579_);
lean_dec(v_a_3578_);
return v_res_3580_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3581_, lean_object* v_x_3582_, size_t v_x_3583_, lean_object* v_x_3584_){
_start:
{
uint8_t v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3582_, v_x_3583_, v_x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
size_t v_x_17067__boxed_3590_; uint8_t v_res_3591_; lean_object* v_r_3592_; 
v_x_17067__boxed_3590_ = lean_unbox_usize(v_x_3588_);
lean_dec(v_x_3588_);
v_res_3591_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3586_, v_x_3587_, v_x_17067__boxed_3590_, v_x_3589_);
lean_dec_ref(v_x_3589_);
lean_dec_ref(v_x_3587_);
v_r_3592_ = lean_box(v_res_3591_);
return v_r_3592_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3593_, lean_object* v_keys_3594_, lean_object* v_vals_3595_, lean_object* v_heq_3596_, lean_object* v_i_3597_, lean_object* v_k_3598_){
_start:
{
uint8_t v___x_3599_; 
v___x_3599_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3594_, v_i_3597_, v_k_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3600_, lean_object* v_keys_3601_, lean_object* v_vals_3602_, lean_object* v_heq_3603_, lean_object* v_i_3604_, lean_object* v_k_3605_){
_start:
{
uint8_t v_res_3606_; lean_object* v_r_3607_; 
v_res_3606_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3600_, v_keys_3601_, v_vals_3602_, v_heq_3603_, v_i_3604_, v_k_3605_);
lean_dec_ref(v_k_3605_);
lean_dec_ref(v_vals_3602_);
lean_dec_ref(v_keys_3601_);
v_r_3607_ = lean_box(v_res_3606_);
return v_r_3607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = lean_box(0);
v___x_3609_ = lean_unsigned_to_nat(16u);
v___x_3610_ = lean_mk_array(v___x_3609_, v___x_3608_);
return v___x_3610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3616_ = lean_st_mk_ref(v___x_3615_);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_ref_3625_; lean_object* v___x_3626_; lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3672_; 
v_ref_3625_ = lean_ctor_get(v___y_3622_, 2);
v___x_3626_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3621_, v___y_3622_, v___y_3623_);
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3672_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3672_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v_traceState_3632_; lean_object* v_env_3633_; lean_object* v_nextMacroScope_3634_; lean_object* v_ngen_3635_; lean_object* v_auxDeclNGen_3636_; lean_object* v_cache_3637_; lean_object* v_recordedDeps_3638_; lean_object* v_messages_3639_; lean_object* v_infoState_3640_; lean_object* v_snapshotTasks_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3671_; 
v___x_3631_ = lean_st_ref_take(v___y_3623_);
v_traceState_3632_ = lean_ctor_get(v___x_3631_, 4);
v_env_3633_ = lean_ctor_get(v___x_3631_, 0);
v_nextMacroScope_3634_ = lean_ctor_get(v___x_3631_, 1);
v_ngen_3635_ = lean_ctor_get(v___x_3631_, 2);
v_auxDeclNGen_3636_ = lean_ctor_get(v___x_3631_, 3);
v_cache_3637_ = lean_ctor_get(v___x_3631_, 5);
v_recordedDeps_3638_ = lean_ctor_get(v___x_3631_, 6);
v_messages_3639_ = lean_ctor_get(v___x_3631_, 7);
v_infoState_3640_ = lean_ctor_get(v___x_3631_, 8);
v_snapshotTasks_3641_ = lean_ctor_get(v___x_3631_, 9);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3643_ = v___x_3631_;
v_isShared_3644_ = v_isSharedCheck_3671_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_snapshotTasks_3641_);
lean_inc(v_infoState_3640_);
lean_inc(v_messages_3639_);
lean_inc(v_recordedDeps_3638_);
lean_inc(v_cache_3637_);
lean_inc(v_traceState_3632_);
lean_inc(v_auxDeclNGen_3636_);
lean_inc(v_ngen_3635_);
lean_inc(v_nextMacroScope_3634_);
lean_inc(v_env_3633_);
lean_dec(v___x_3631_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3671_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
uint64_t v_tid_3645_; lean_object* v_traces_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3670_; 
v_tid_3645_ = lean_ctor_get_uint64(v_traceState_3632_, sizeof(void*)*1);
v_traces_3646_ = lean_ctor_get(v_traceState_3632_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_traceState_3632_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3648_ = v_traceState_3632_;
v_isShared_3649_ = v_isSharedCheck_3670_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_traces_3646_);
lean_dec(v_traceState_3632_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3670_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; double v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_box(0);
v___x_3652_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3653_ = 0;
v___x_3654_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3655_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3655_, 0, v_cls_3620_);
lean_ctor_set(v___x_3655_, 1, v___x_3651_);
lean_ctor_set(v___x_3655_, 2, v___x_3654_);
lean_ctor_set_float(v___x_3655_, sizeof(void*)*3, v___x_3652_);
lean_ctor_set_float(v___x_3655_, sizeof(void*)*3 + 8, v___x_3652_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*3 + 16, v___x_3653_);
v___x_3656_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3657_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v_a_3627_);
lean_ctor_set(v___x_3657_, 2, v___x_3656_);
lean_inc(v_ref_3625_);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_ref_3625_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Lean_PersistentArray_push___redArg(v_traces_3646_, v___x_3658_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3659_);
v___x_3661_ = v___x_3648_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3659_);
lean_ctor_set_uint64(v_reuseFailAlloc_3669_, sizeof(void*)*1, v_tid_3645_);
v___x_3661_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 4, v___x_3661_);
v___x_3663_ = v___x_3643_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_env_3633_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_nextMacroScope_3634_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_ngen_3635_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_auxDeclNGen_3636_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3668_, 5, v_cache_3637_);
lean_ctor_set(v_reuseFailAlloc_3668_, 6, v_recordedDeps_3638_);
lean_ctor_set(v_reuseFailAlloc_3668_, 7, v_messages_3639_);
lean_ctor_set(v_reuseFailAlloc_3668_, 8, v_infoState_3640_);
lean_ctor_set(v_reuseFailAlloc_3668_, 9, v_snapshotTasks_3641_);
v___x_3663_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_st_ref_put(v___y_3623_, v___x_3663_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3650_);
v___x_3666_ = v___x_3629_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3650_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3673_, lean_object* v_msg_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3673_, v_msg_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3679_, uint8_t v_isMeta_3680_, lean_object* v_hint_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v_env_3703_; uint8_t v_isExporting_3704_; lean_object* v_entry_3705_; lean_object* v___x_3706_; lean_object* v_env_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3701_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_3702_ = lean_st_ref_get(v___y_3683_);
v_env_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc_ref(v_env_3703_);
lean_dec(v___x_3702_);
v_isExporting_3704_ = lean_ctor_get_uint8(v_env_3703_, sizeof(void*)*13);
lean_dec_ref(v_env_3703_);
lean_inc(v_mod_3679_);
v_entry_3705_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3705_, 0, v_mod_3679_);
lean_ctor_set_uint8(v_entry_3705_, sizeof(void*)*1, v_isExporting_3704_);
lean_ctor_set_uint8(v_entry_3705_, sizeof(void*)*1 + 1, v_isMeta_3680_);
v___x_3706_ = lean_st_ref_get(v___y_3683_);
v_env_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc_ref(v_env_3707_);
lean_dec(v___x_3706_);
v___x_3708_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3709_ = lean_box(1);
v___x_3710_ = lean_box(0);
v___x_3711_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3701_, v___x_3708_, v_env_3707_, v___x_3709_, v___x_3710_);
v___x_3712_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3711_, v_entry_3705_);
lean_dec(v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v_toCold_3713_; lean_object* v_options_3714_; lean_object* v_inheritedTraceOptions_3715_; uint8_t v_hasTrace_3716_; lean_object* v___f_3717_; uint8_t v___x_3718_; lean_object* v___y_3720_; 
v_toCold_3713_ = lean_ctor_get(v___y_3682_, 0);
v_options_3714_ = lean_ctor_get(v_toCold_3713_, 2);
v_inheritedTraceOptions_3715_ = lean_ctor_get(v_toCold_3713_, 11);
v_hasTrace_3716_ = lean_ctor_get_uint8(v_options_3714_, sizeof(void*)*1);
v___f_3717_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_3717_, 0, v___x_3708_);
lean_closure_set(v___f_3717_, 1, v_entry_3705_);
v___x_3718_ = 1;
if (v_hasTrace_3716_ == 0)
{
lean_dec(v_hint_3681_);
lean_dec(v_mod_3679_);
v___y_3720_ = v___y_3683_;
goto v___jp_3719_;
}
else
{
lean_object* v_cls_3738_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_cls_3738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_3758_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_3759_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3715_, v_options_3714_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_dec(v_hint_3681_);
lean_dec(v_mod_3679_);
v___y_3720_ = v___y_3683_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3760_; lean_object* v___y_3762_; 
v___x_3760_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_3704_ == 0)
{
lean_object* v___x_3769_; 
v___x_3769_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3762_ = v___x_3769_;
goto v___jp_3761_;
}
else
{
lean_object* v___x_3770_; 
v___x_3770_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3762_ = v___x_3770_;
goto v___jp_3761_;
}
v___jp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc_ref(v___y_3762_);
v___x_3763_ = l_Lean_stringToMessageData(v___y_3762_);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3760_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
if (v_isMeta_3680_ == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_3745_ = v___x_3766_;
v___y_3746_ = v___x_3767_;
goto v___jp_3744_;
}
else
{
lean_object* v___x_3768_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_3745_ = v___x_3766_;
v___y_3746_ = v___x_3768_;
goto v___jp_3744_;
}
}
}
v___jp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___y_3740_);
lean_ctor_set(v___x_3742_, 1, v___y_3741_);
v___x_3743_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3738_, v___x_3742_, v___y_3682_, v___y_3683_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_dec_ref_known(v___x_3743_, 1);
v___y_3720_ = v___y_3683_;
goto v___jp_3719_;
}
else
{
lean_dec_ref(v___f_3717_);
return v___x_3743_;
}
}
v___jp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
lean_inc_ref(v___y_3746_);
v___x_3747_ = l_Lean_stringToMessageData(v___y_3746_);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___y_3745_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l_Lean_MessageData_ofName(v_mod_3679_);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = l_Lean_Name_isAnonymous(v_hint_3681_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3755_ = l_Lean_MessageData_ofName(v_hint_3681_);
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___y_3740_ = v___x_3752_;
v___y_3741_ = v___x_3756_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3757_; 
lean_dec(v_hint_3681_);
v___x_3757_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_3740_ = v___x_3752_;
v___y_3741_ = v___x_3757_;
goto v___jp_3739_;
}
}
}
v___jp_3719_:
{
lean_object* v___x_3721_; lean_object* v_toEnvExtension_3722_; lean_object* v_env_3723_; lean_object* v_nextMacroScope_3724_; lean_object* v_ngen_3725_; lean_object* v_auxDeclNGen_3726_; lean_object* v_traceState_3727_; lean_object* v_recordedDeps_3728_; lean_object* v_messages_3729_; lean_object* v_infoState_3730_; lean_object* v_snapshotTasks_3731_; lean_object* v_asyncMode_3732_; uint8_t v_logWrites_3733_; lean_object* v___x_3734_; 
v___x_3721_ = lean_st_ref_take(v___y_3720_);
v_toEnvExtension_3722_ = lean_ctor_get(v___x_3708_, 0);
v_env_3723_ = lean_ctor_get(v___x_3721_, 0);
lean_inc_ref(v_env_3723_);
v_nextMacroScope_3724_ = lean_ctor_get(v___x_3721_, 1);
lean_inc(v_nextMacroScope_3724_);
v_ngen_3725_ = lean_ctor_get(v___x_3721_, 2);
lean_inc_ref(v_ngen_3725_);
v_auxDeclNGen_3726_ = lean_ctor_get(v___x_3721_, 3);
lean_inc_ref(v_auxDeclNGen_3726_);
v_traceState_3727_ = lean_ctor_get(v___x_3721_, 4);
lean_inc_ref(v_traceState_3727_);
v_recordedDeps_3728_ = lean_ctor_get(v___x_3721_, 6);
lean_inc_ref(v_recordedDeps_3728_);
v_messages_3729_ = lean_ctor_get(v___x_3721_, 7);
lean_inc_ref(v_messages_3729_);
v_infoState_3730_ = lean_ctor_get(v___x_3721_, 8);
lean_inc_ref(v_infoState_3730_);
v_snapshotTasks_3731_ = lean_ctor_get(v___x_3721_, 9);
lean_inc_ref(v_snapshotTasks_3731_);
lean_dec(v___x_3721_);
v_asyncMode_3732_ = lean_ctor_get(v_toEnvExtension_3722_, 2);
v_logWrites_3733_ = lean_ctor_get_uint8(v_toEnvExtension_3722_, sizeof(void*)*6);
v___x_3734_ = lean_box(0);
if (v_logWrites_3733_ == 0)
{
lean_object* v___x_3735_; 
lean_inc_ref(v_toEnvExtension_3722_);
v___x_3735_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3722_, v_env_3723_, v___f_3717_, v_asyncMode_3732_, v___x_3710_, v___x_3718_);
v___y_3686_ = v___y_3720_;
v___y_3687_ = v_auxDeclNGen_3726_;
v___y_3688_ = v_nextMacroScope_3724_;
v___y_3689_ = v_recordedDeps_3728_;
v___y_3690_ = v_traceState_3727_;
v___y_3691_ = v_infoState_3730_;
v___y_3692_ = v_messages_3729_;
v___y_3693_ = v_ngen_3725_;
v___y_3694_ = v___x_3734_;
v___y_3695_ = v_snapshotTasks_3731_;
v___y_3696_ = v___x_3735_;
goto v___jp_3685_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_inc_ref_n(v_toEnvExtension_3722_, 2);
v___x_3736_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3722_, v_env_3723_);
lean_dec_ref(v_env_3723_);
v___x_3737_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3722_, v___x_3736_, v___f_3717_, v_asyncMode_3732_, v___x_3710_, v___x_3718_);
v___y_3686_ = v___y_3720_;
v___y_3687_ = v_auxDeclNGen_3726_;
v___y_3688_ = v_nextMacroScope_3724_;
v___y_3689_ = v_recordedDeps_3728_;
v___y_3690_ = v_traceState_3727_;
v___y_3691_ = v_infoState_3730_;
v___y_3692_ = v_messages_3729_;
v___y_3693_ = v_ngen_3725_;
v___y_3694_ = v___x_3734_;
v___y_3695_ = v_snapshotTasks_3731_;
v___y_3696_ = v___x_3737_;
goto v___jp_3685_;
}
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_dec_ref_known(v_entry_3705_, 1);
lean_dec(v_hint_3681_);
lean_dec(v_mod_3679_);
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
v___jp_3685_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_3698_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3696_);
lean_ctor_set(v___x_3698_, 1, v___y_3688_);
lean_ctor_set(v___x_3698_, 2, v___y_3693_);
lean_ctor_set(v___x_3698_, 3, v___y_3687_);
lean_ctor_set(v___x_3698_, 4, v___y_3690_);
lean_ctor_set(v___x_3698_, 5, v___x_3697_);
lean_ctor_set(v___x_3698_, 6, v___y_3689_);
lean_ctor_set(v___x_3698_, 7, v___y_3692_);
lean_ctor_set(v___x_3698_, 8, v___y_3691_);
lean_ctor_set(v___x_3698_, 9, v___y_3695_);
v___x_3699_ = lean_st_ref_put(v___y_3686_, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___y_3694_);
return v___x_3700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3773_, lean_object* v_isMeta_3774_, lean_object* v_hint_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
uint8_t v_isMeta_boxed_3779_; lean_object* v_res_3780_; 
v_isMeta_boxed_3779_ = lean_unbox(v_isMeta_3774_);
v_res_3780_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3773_, v_isMeta_boxed_3779_, v_hint_3775_, v___y_3776_, v___y_3777_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3781_, lean_object* v_declName_3782_, lean_object* v_as_3783_, size_t v_sz_3784_, size_t v_i_3785_, lean_object* v_b_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
uint8_t v___x_3790_; 
v___x_3790_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec(v_declName_3782_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_b_3786_);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v_modules_3793_; lean_object* v___x_3794_; lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v_toImport_3797_; lean_object* v_module_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; 
v___x_3792_ = l_Lean_Environment_header(v___x_3781_);
v_modules_3793_ = lean_ctor_get(v___x_3792_, 3);
lean_inc_ref(v_modules_3793_);
lean_dec_ref(v___x_3792_);
v___x_3794_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3795_ = lean_array_uget_borrowed(v_as_3783_, v_i_3785_);
v___x_3796_ = lean_array_get(v___x_3794_, v_modules_3793_, v_a_3795_);
lean_dec_ref(v_modules_3793_);
v_toImport_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc_ref(v_toImport_3797_);
lean_dec(v___x_3796_);
v_module_3798_ = lean_ctor_get(v_toImport_3797_, 0);
lean_inc(v_module_3798_);
lean_dec_ref(v_toImport_3797_);
v___x_3799_ = lean_box(0);
v___x_3800_ = 0;
lean_inc(v_declName_3782_);
v___x_3801_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3798_, v___x_3800_, v_declName_3782_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3801_) == 0)
{
size_t v___x_3802_; size_t v___x_3803_; 
lean_dec_ref_known(v___x_3801_, 1);
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3785_, v___x_3802_);
v_i_3785_ = v___x_3803_;
v_b_3786_ = v___x_3799_;
goto _start;
}
else
{
lean_dec(v_declName_3782_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3805_, lean_object* v_declName_3806_, lean_object* v_as_3807_, lean_object* v_sz_3808_, lean_object* v_i_3809_, lean_object* v_b_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
size_t v_sz_boxed_3814_; size_t v_i_boxed_3815_; lean_object* v_res_3816_; 
v_sz_boxed_3814_ = lean_unbox_usize(v_sz_3808_);
lean_dec(v_sz_3808_);
v_i_boxed_3815_ = lean_unbox_usize(v_i_3809_);
lean_dec(v_i_3809_);
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3805_, v_declName_3806_, v_as_3807_, v_sz_boxed_3814_, v_i_boxed_3815_, v_b_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v_as_3807_);
lean_dec_ref(v___x_3805_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3817_, uint8_t v_isMeta_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v_env_3827_; lean_object* v___y_3829_; lean_object* v___x_3842_; 
v___x_3822_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3823_ = lean_st_ref_get(v___y_3820_);
v_env_3827_ = lean_ctor_get(v___x_3823_, 0);
lean_inc_ref(v_env_3827_);
lean_dec(v___x_3823_);
v___x_3842_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3827_, v_declName_3817_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_dec_ref(v_env_3827_);
lean_dec(v_declName_3817_);
goto v___jp_3824_;
}
else
{
lean_object* v_val_3843_; lean_object* v___x_3844_; lean_object* v_modules_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_val_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_val_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = l_Lean_Environment_header(v_env_3827_);
v_modules_3845_ = lean_ctor_get(v___x_3844_, 3);
lean_inc_ref(v_modules_3845_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = lean_array_get_size(v_modules_3845_);
v___x_3847_ = lean_nat_dec_lt(v_val_3843_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_dec_ref(v_modules_3845_);
lean_dec(v_val_3843_);
lean_dec_ref(v_env_3827_);
lean_dec(v_declName_3817_);
goto v___jp_3824_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___y_3851_; 
v___x_3848_ = lean_array_fget(v_modules_3845_, v_val_3843_);
lean_dec(v_val_3843_);
lean_dec_ref(v_modules_3845_);
v___x_3849_ = lean_st_ref_get(v___y_3820_);
if (v_isMeta_3818_ == 0)
{
lean_dec(v___x_3849_);
v___y_3851_ = v_isMeta_3818_;
goto v___jp_3850_;
}
else
{
lean_object* v_env_3862_; uint8_t v___x_3863_; 
v_env_3862_ = lean_ctor_get(v___x_3849_, 0);
lean_inc_ref(v_env_3862_);
lean_dec(v___x_3849_);
lean_inc(v_declName_3817_);
v___x_3863_ = l_Lean_isMarkedMeta(v_env_3862_, v_declName_3817_);
if (v___x_3863_ == 0)
{
v___y_3851_ = v_isMeta_3818_;
goto v___jp_3850_;
}
else
{
uint8_t v___x_3864_; 
v___x_3864_ = 0;
v___y_3851_ = v___x_3864_;
goto v___jp_3850_;
}
}
v___jp_3850_:
{
lean_object* v_toImport_3852_; lean_object* v_module_3853_; lean_object* v___x_3854_; 
v_toImport_3852_ = lean_ctor_get(v___x_3848_, 0);
lean_inc_ref(v_toImport_3852_);
lean_dec(v___x_3848_);
v_module_3853_ = lean_ctor_get(v_toImport_3852_, 0);
lean_inc(v_module_3853_);
lean_dec_ref(v_toImport_3852_);
lean_inc(v_declName_3817_);
v___x_3854_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3853_, v___y_3851_, v_declName_3817_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref_known(v___x_3854_, 1);
v___x_3855_ = l_Lean_indirectModUseExt;
v___x_3856_ = lean_box(1);
v___x_3857_ = lean_box(0);
lean_inc_ref(v_env_3827_);
v___x_3858_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3822_, v___x_3855_, v_env_3827_, v___x_3856_, v___x_3857_);
v___x_3859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3858_, v_declName_3817_);
lean_dec(v___x_3858_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; 
v___x_3860_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3829_ = v___x_3860_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3861_; 
v_val_3861_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_val_3861_);
lean_dec_ref_known(v___x_3859_, 1);
v___y_3829_ = v_val_3861_;
goto v___jp_3828_;
}
}
else
{
lean_dec_ref(v_env_3827_);
lean_dec(v_declName_3817_);
return v___x_3854_;
}
}
}
}
v___jp_3824_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
v___jp_3828_:
{
lean_object* v___x_3830_; size_t v_sz_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3830_ = lean_box(0);
v_sz_3831_ = lean_array_size(v___y_3829_);
v___x_3832_ = ((size_t)0ULL);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3827_, v_declName_3817_, v___y_3829_, v_sz_3831_, v___x_3832_, v___x_3830_, v___y_3819_, v___y_3820_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_env_3827_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v___x_3833_, 0);
lean_dec(v_unused_3841_);
v___x_3835_ = v___x_3833_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_dec(v___x_3833_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3830_);
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3830_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
else
{
return v___x_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3865_, lean_object* v_isMeta_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
uint8_t v_isMeta_boxed_3870_; lean_object* v_res_3871_; 
v_isMeta_boxed_3870_ = lean_unbox(v_isMeta_3866_);
v_res_3871_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3865_, v_isMeta_boxed_3870_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3877_ = lean_st_ref_get(v___x_3876_);
v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3877_, v_attrName_3872_);
lean_dec(v___x_3877_);
if (lean_obj_tag(v___x_3878_) == 1)
{
lean_object* v_val_3879_; lean_object* v_ext_3880_; lean_object* v_name_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; 
v_val_3879_ = lean_ctor_get(v___x_3878_, 0);
v_ext_3880_ = lean_ctor_get(v_val_3879_, 1);
v_name_3881_ = lean_ctor_get(v_ext_3880_, 1);
v___x_3882_ = 1;
lean_inc(v_name_3881_);
v___x_3883_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3881_, v___x_3882_, v_a_3873_, v_a_3874_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3883_, 0);
lean_dec(v_unused_3891_);
v___x_3885_ = v___x_3883_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_dec(v___x_3883_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3878_);
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3878_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref_known(v___x_3878_, 1);
v_a_3892_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3883_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3883_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3878_);
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_attrName_3901_);
return v_res_3905_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3907_, lean_object* v_x_3908_){
_start:
{
if (lean_obj_tag(v_x_3908_) == 0)
{
return v_x_3907_;
}
else
{
lean_object* v_key_3909_; lean_object* v_value_3910_; lean_object* v_tail_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3937_; 
v_key_3909_ = lean_ctor_get(v_x_3908_, 0);
v_value_3910_ = lean_ctor_get(v_x_3908_, 1);
v_tail_3911_ = lean_ctor_get(v_x_3908_, 2);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3908_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3913_ = v_x_3908_;
v_isShared_3914_ = v_isSharedCheck_3937_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_tail_3911_);
lean_inc(v_value_3910_);
lean_inc(v_key_3909_);
lean_dec(v_x_3908_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3937_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3915_; uint64_t v___y_3917_; 
v___x_3915_ = lean_array_get_size(v_x_3907_);
if (lean_obj_tag(v_key_3909_) == 0)
{
uint64_t v___x_3935_; 
v___x_3935_ = 1723ULL;
v___y_3917_ = v___x_3935_;
goto v___jp_3916_;
}
else
{
uint64_t v_hash_3936_; 
v_hash_3936_ = lean_ctor_get_uint64(v_key_3909_, sizeof(void*)*2);
v___y_3917_ = v_hash_3936_;
goto v___jp_3916_;
}
v___jp_3916_:
{
uint64_t v___x_3918_; uint64_t v___x_3919_; uint64_t v_fold_3920_; uint64_t v___x_3921_; uint64_t v___x_3922_; uint64_t v___x_3923_; size_t v___x_3924_; size_t v___x_3925_; size_t v___x_3926_; size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3918_ = 32ULL;
v___x_3919_ = lean_uint64_shift_right(v___y_3917_, v___x_3918_);
v_fold_3920_ = lean_uint64_xor(v___y_3917_, v___x_3919_);
v___x_3921_ = 16ULL;
v___x_3922_ = lean_uint64_shift_right(v_fold_3920_, v___x_3921_);
v___x_3923_ = lean_uint64_xor(v_fold_3920_, v___x_3922_);
v___x_3924_ = lean_uint64_to_usize(v___x_3923_);
v___x_3925_ = lean_usize_of_nat(v___x_3915_);
v___x_3926_ = ((size_t)1ULL);
v___x_3927_ = lean_usize_sub(v___x_3925_, v___x_3926_);
v___x_3928_ = lean_usize_land(v___x_3924_, v___x_3927_);
v___x_3929_ = lean_array_uget_borrowed(v_x_3907_, v___x_3928_);
lean_inc(v___x_3929_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 2, v___x_3929_);
v___x_3931_ = v___x_3913_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_key_3909_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_value_3910_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_array_uset(v_x_3907_, v___x_3928_, v___x_3931_);
v_x_3907_ = v___x_3932_;
v_x_3908_ = v_tail_3911_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3938_, lean_object* v_source_3939_, lean_object* v_target_3940_){
_start:
{
lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3941_ = lean_array_get_size(v_source_3939_);
v___x_3942_ = lean_nat_dec_lt(v_i_3938_, v___x_3941_);
if (v___x_3942_ == 0)
{
lean_dec_ref(v_source_3939_);
lean_dec(v_i_3938_);
return v_target_3940_;
}
else
{
lean_object* v_es_3943_; lean_object* v___x_3944_; lean_object* v_source_3945_; lean_object* v_target_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_es_3943_ = lean_array_fget(v_source_3939_, v_i_3938_);
v___x_3944_ = lean_box(0);
v_source_3945_ = lean_array_fset(v_source_3939_, v_i_3938_, v___x_3944_);
v_target_3946_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3940_, v_es_3943_);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_add(v_i_3938_, v___x_3947_);
lean_dec(v_i_3938_);
v_i_3938_ = v___x_3948_;
v_source_3939_ = v_source_3945_;
v_target_3940_ = v_target_3946_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3950_){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v_nbuckets_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3951_ = lean_array_get_size(v_data_3950_);
v___x_3952_ = lean_unsigned_to_nat(2u);
v_nbuckets_3953_ = lean_nat_mul(v___x_3951_, v___x_3952_);
v___x_3954_ = lean_unsigned_to_nat(0u);
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_mk_array(v_nbuckets_3953_, v___x_3955_);
v___x_3957_ = lean_array_propagate_mark(v_data_3950_, v___x_3956_);
v___x_3958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3954_, v_data_3950_, v___x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3959_, lean_object* v_x_3960_){
_start:
{
if (lean_obj_tag(v_x_3960_) == 0)
{
uint8_t v___x_3961_; 
v___x_3961_ = 0;
return v___x_3961_;
}
else
{
lean_object* v_key_3962_; lean_object* v_tail_3963_; uint8_t v___x_3964_; 
v_key_3962_ = lean_ctor_get(v_x_3960_, 0);
v_tail_3963_ = lean_ctor_get(v_x_3960_, 2);
v___x_3964_ = lean_name_eq(v_key_3962_, v_a_3959_);
if (v___x_3964_ == 0)
{
v_x_3960_ = v_tail_3963_;
goto _start;
}
else
{
return v___x_3964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3966_, lean_object* v_x_3967_){
_start:
{
uint8_t v_res_3968_; lean_object* v_r_3969_; 
v_res_3968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3966_, v_x_3967_);
lean_dec(v_x_3967_);
lean_dec(v_a_3966_);
v_r_3969_ = lean_box(v_res_3968_);
return v_r_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3970_, lean_object* v_b_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
lean_dec(v_b_3971_);
lean_dec(v_a_3970_);
return v_x_3972_;
}
else
{
lean_object* v_key_3973_; lean_object* v_value_3974_; lean_object* v_tail_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3987_; 
v_key_3973_ = lean_ctor_get(v_x_3972_, 0);
v_value_3974_ = lean_ctor_get(v_x_3972_, 1);
v_tail_3975_ = lean_ctor_get(v_x_3972_, 2);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_x_3972_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3977_ = v_x_3972_;
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_tail_3975_);
lean_inc(v_value_3974_);
lean_inc(v_key_3973_);
lean_dec(v_x_3972_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3987_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_name_eq(v_key_3973_, v_a_3970_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3970_, v_b_3971_, v_tail_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 2, v___x_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_key_3973_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_value_3974_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
else
{
lean_object* v___x_3985_; 
lean_dec(v_value_3974_);
lean_dec(v_key_3973_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v_b_3971_);
lean_ctor_set(v___x_3977_, 0, v_a_3970_);
v___x_3985_ = v___x_3977_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3970_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_b_3971_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_tail_3975_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3988_, lean_object* v_a_3989_, lean_object* v_b_3990_){
_start:
{
lean_object* v_size_3991_; lean_object* v_buckets_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4038_; 
v_size_3991_ = lean_ctor_get(v_m_3988_, 0);
v_buckets_3992_ = lean_ctor_get(v_m_3988_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_m_3988_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_3994_ = v_m_3988_;
v_isShared_3995_ = v_isSharedCheck_4038_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_buckets_3992_);
lean_inc(v_size_3991_);
lean_dec(v_m_3988_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4038_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; uint64_t v___y_3998_; 
v___x_3996_ = lean_array_get_size(v_buckets_3992_);
if (lean_obj_tag(v_a_3989_) == 0)
{
uint64_t v___x_4036_; 
v___x_4036_ = 1723ULL;
v___y_3998_ = v___x_4036_;
goto v___jp_3997_;
}
else
{
uint64_t v_hash_4037_; 
v_hash_4037_ = lean_ctor_get_uint64(v_a_3989_, sizeof(void*)*2);
v___y_3998_ = v_hash_4037_;
goto v___jp_3997_;
}
v___jp_3997_:
{
uint64_t v___x_3999_; uint64_t v___x_4000_; uint64_t v_fold_4001_; uint64_t v___x_4002_; uint64_t v___x_4003_; uint64_t v___x_4004_; size_t v___x_4005_; size_t v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; size_t v___x_4009_; lean_object* v_bkt_4010_; uint8_t v___x_4011_; 
v___x_3999_ = 32ULL;
v___x_4000_ = lean_uint64_shift_right(v___y_3998_, v___x_3999_);
v_fold_4001_ = lean_uint64_xor(v___y_3998_, v___x_4000_);
v___x_4002_ = 16ULL;
v___x_4003_ = lean_uint64_shift_right(v_fold_4001_, v___x_4002_);
v___x_4004_ = lean_uint64_xor(v_fold_4001_, v___x_4003_);
v___x_4005_ = lean_uint64_to_usize(v___x_4004_);
v___x_4006_ = lean_usize_of_nat(v___x_3996_);
v___x_4007_ = ((size_t)1ULL);
v___x_4008_ = lean_usize_sub(v___x_4006_, v___x_4007_);
v___x_4009_ = lean_usize_land(v___x_4005_, v___x_4008_);
v_bkt_4010_ = lean_array_uget_borrowed(v_buckets_3992_, v___x_4009_);
v___x_4011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3989_, v_bkt_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v_size_x27_4013_; lean_object* v___x_4014_; lean_object* v_buckets_x27_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4012_ = lean_unsigned_to_nat(1u);
v_size_x27_4013_ = lean_nat_add(v_size_3991_, v___x_4012_);
lean_dec(v_size_3991_);
lean_inc(v_bkt_4010_);
v___x_4014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4014_, 0, v_a_3989_);
lean_ctor_set(v___x_4014_, 1, v_b_3990_);
lean_ctor_set(v___x_4014_, 2, v_bkt_4010_);
v_buckets_x27_4015_ = lean_array_uset(v_buckets_3992_, v___x_4009_, v___x_4014_);
v___x_4016_ = lean_unsigned_to_nat(4u);
v___x_4017_ = lean_nat_mul(v_size_x27_4013_, v___x_4016_);
v___x_4018_ = lean_unsigned_to_nat(3u);
v___x_4019_ = lean_nat_div(v___x_4017_, v___x_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_array_get_size(v_buckets_x27_4015_);
v___x_4021_ = lean_nat_dec_le(v___x_4019_, v___x_4020_);
lean_dec(v___x_4019_);
if (v___x_4021_ == 0)
{
lean_object* v_val_4022_; lean_object* v___x_4024_; 
v_val_4022_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4015_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 1, v_val_4022_);
lean_ctor_set(v___x_3994_, 0, v_size_x27_4013_);
v___x_4024_ = v___x_3994_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_size_x27_4013_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v_val_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
else
{
lean_object* v___x_4027_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 1, v_buckets_x27_4015_);
lean_ctor_set(v___x_3994_, 0, v_size_x27_4013_);
v___x_4027_ = v___x_3994_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_size_x27_4013_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_buckets_x27_4015_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
else
{
lean_object* v___x_4029_; lean_object* v_buckets_x27_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_inc(v_bkt_4010_);
v___x_4029_ = lean_box(0);
v_buckets_x27_4030_ = lean_array_uset(v_buckets_3992_, v___x_4009_, v___x_4029_);
v___x_4031_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3989_, v_b_3990_, v_bkt_4010_);
v___x_4032_ = lean_array_uset(v_buckets_x27_4030_, v___x_4009_, v___x_4031_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 1, v___x_4032_);
v___x_4034_ = v___x_3994_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_size_3991_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4039_, lean_object* v_ref_4040_){
_start:
{
lean_object* v___x_4042_; 
lean_inc(v_ref_4040_);
v___x_4042_ = l_Lean_Meta_Grind_mkExtension(v_ref_4040_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; uint8_t v___x_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc_n(v_a_4043_, 2);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = 0;
v___x_4045_ = 1;
lean_inc(v_ref_4040_);
lean_inc(v_attrName_4039_);
v___x_4046_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4039_, v___x_4044_, v___x_4045_, v_a_4043_, v_ref_4040_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v___x_4047_; 
lean_dec_ref_known(v___x_4046_, 1);
lean_inc(v_ref_4040_);
lean_inc(v_a_4043_);
lean_inc(v_attrName_4039_);
v___x_4047_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4039_, v___x_4044_, v___x_4044_, v_a_4043_, v_ref_4040_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v___x_4048_; 
lean_dec_ref_known(v___x_4047_, 1);
lean_inc(v_ref_4040_);
lean_inc(v_a_4043_);
lean_inc(v_attrName_4039_);
v___x_4048_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4039_, v___x_4045_, v___x_4045_, v_a_4043_, v_ref_4040_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v___x_4049_; 
lean_dec_ref_known(v___x_4048_, 1);
lean_inc(v_a_4043_);
lean_inc(v_attrName_4039_);
v___x_4049_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4039_, v___x_4045_, v___x_4044_, v_a_4043_, v_ref_4040_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4060_; 
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4049_, 0);
lean_dec(v_unused_4061_);
v___x_4051_ = v___x_4049_;
v_isShared_4052_ = v_isSharedCheck_4060_;
goto v_resetjp_4050_;
}
else
{
lean_dec(v___x_4049_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4060_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4053_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4054_ = lean_st_ref_take(v___x_4053_);
lean_inc(v_a_4043_);
v___x_4055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4054_, v_attrName_4039_, v_a_4043_);
v___x_4056_ = lean_st_ref_put(v___x_4053_, v___x_4055_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v_a_4043_);
v___x_4058_ = v___x_4051_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4043_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_a_4043_);
lean_dec(v_attrName_4039_);
v_a_4062_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4049_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4049_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_a_4043_);
lean_dec(v_ref_4040_);
lean_dec(v_attrName_4039_);
v_a_4070_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4048_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4048_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v_a_4043_);
lean_dec(v_ref_4040_);
lean_dec(v_attrName_4039_);
v_a_4078_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4047_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4047_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_a_4043_);
lean_dec(v_ref_4040_);
lean_dec(v_attrName_4039_);
v_a_4086_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4046_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4046_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
lean_dec(v_ref_4040_);
lean_dec(v_attrName_4039_);
return v___x_4042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4094_, lean_object* v_ref_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4094_, v_ref_4095_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4098_, lean_object* v_m_4099_, lean_object* v_a_4100_, lean_object* v_b_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4099_, v_a_4100_, v_b_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4103_, lean_object* v_a_4104_, lean_object* v_x_4105_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4104_, v_x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4107_, lean_object* v_a_4108_, lean_object* v_x_4109_){
_start:
{
uint8_t v_res_4110_; lean_object* v_r_4111_; 
v_res_4110_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4107_, v_a_4108_, v_x_4109_);
lean_dec(v_x_4109_);
lean_dec(v_a_4108_);
v_r_4111_ = lean_box(v_res_4110_);
return v_r_4111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4112_, lean_object* v_data_4113_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4115_, lean_object* v_a_4116_, lean_object* v_b_4117_, lean_object* v_x_4118_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4116_, v_b_4117_, v_x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4120_, lean_object* v_i_4121_, lean_object* v_source_4122_, lean_object* v_target_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4121_, v_source_4122_, v_target_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4125_, lean_object* v_x_4126_, lean_object* v_x_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4126_, v_x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4137_ = l_Lean_Meta_Grind_registerAttr(v___x_4135_, v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4152_ = l_Lean_Meta_Grind_registerAttr(v___x_4150_, v___x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v_env_4160_; lean_object* v___x_4161_; lean_object* v_ext_4162_; lean_object* v_toEnvExtension_4163_; lean_object* v_asyncMode_4164_; uint8_t v___x_4165_; lean_object* v___x_4166_; lean_object* v_casesTypes_4167_; uint8_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4158_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4159_ = lean_st_ref_get(v_a_4156_);
v_env_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc_ref(v_env_4160_);
lean_dec(v___x_4159_);
v___x_4161_ = l_Lean_Meta_Grind_grindExt;
v_ext_4162_ = lean_ctor_get(v___x_4161_, 1);
v_toEnvExtension_4163_ = lean_ctor_get(v_ext_4162_, 0);
v_asyncMode_4164_ = lean_ctor_get(v_toEnvExtension_4163_, 2);
v___x_4165_ = 0;
v___x_4166_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4158_, v___x_4161_, v_env_4160_, v_asyncMode_4164_, v___x_4165_);
v_casesTypes_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc_ref(v_casesTypes_4167_);
lean_dec(v___x_4166_);
v___x_4168_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4167_, v_declName_4155_);
lean_dec_ref(v_casesTypes_4167_);
v___x_4169_ = lean_box(v___x_4168_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4171_, v_a_4172_);
lean_dec(v_a_4172_);
lean_dec(v_declName_4171_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4175_, v_a_4177_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4180_, v_a_4181_, v_a_4182_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_declName_4180_);
return v_res_4184_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
