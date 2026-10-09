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
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_13_;
v_res_13_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_tag_nat(v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_20_, lean_object* v_k_21_){
_start:
{
switch(lean_obj_tag(v_t_20_))
{
case 0:
{
lean_object* v_k_22_; lean_object* v___x_23_; 
v_k_22_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_k_22_);
lean_dec_ref_known(v_t_20_, 1);
v___x_23_ = lean_apply_1(v_k_21_, v_k_22_);
return v___x_23_;
}
case 1:
{
uint8_t v_eager_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_eager_24_ = lean_ctor_get_uint8(v_t_20_, 0);
lean_dec_ref_known(v_t_20_, 0);
v___x_25_ = lean_box(v_eager_24_);
v___x_26_ = lean_apply_1(v_k_21_, v___x_25_);
return v___x_26_;
}
case 5:
{
lean_object* v_prio_27_; lean_object* v___x_28_; 
v_prio_27_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_prio_27_);
lean_dec_ref_known(v_t_20_, 1);
v___x_28_ = lean_apply_1(v_k_21_, v_prio_27_);
return v___x_28_;
}
case 8:
{
uint8_t v_post_29_; uint8_t v_inv_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_post_29_ = lean_ctor_get_uint8(v_t_20_, 0);
v_inv_30_ = lean_ctor_get_uint8(v_t_20_, 1);
lean_dec_ref_known(v_t_20_, 0);
v___x_31_ = lean_box(v_post_29_);
v___x_32_ = lean_box(v_inv_30_);
v___x_33_ = lean_apply_2(v_k_21_, v___x_31_, v___x_32_);
return v___x_33_;
}
case 10:
{
uint8_t v_fallback_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_fallback_34_ = lean_ctor_get_uint8(v_t_20_, 0);
lean_dec_ref_known(v_t_20_, 0);
v___x_35_ = lean_box(v_fallback_34_);
v___x_36_ = lean_apply_1(v_k_21_, v___x_35_);
return v___x_36_;
}
default: 
{
lean_dec(v_t_20_);
return v_k_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_39_, v_k_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_43_, v_ctorIdx_44_, v_t_45_, v_h_46_, v_k_47_);
lean_dec(v_ctorIdx_44_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_49_, lean_object* v_ematch_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_49_, v_ematch_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_ematch_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_53_, v_ematch_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_57_, lean_object* v_cases_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_57_, v_cases_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_cases_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_61_, v_cases_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_65_, lean_object* v_intro_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_65_, v_intro_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_intro_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_69_, v_intro_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_73_, lean_object* v_infer_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_73_, v_infer_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_infer_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_77_, v_infer_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_81_, lean_object* v_ext_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_81_, v_ext_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_ext_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_85_, v_ext_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_89_, lean_object* v_symbol_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_89_, v_symbol_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_symbol_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_93_, v_symbol_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_97_, lean_object* v_inj_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_97_, v_inj_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_inj_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_101_, v_inj_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_105_, lean_object* v_funCC_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_105_, v_funCC_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_funCC_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_109_, v_funCC_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_113_, lean_object* v_norm_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_113_, v_norm_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_norm_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_117_, v_norm_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_121_, lean_object* v_unfold_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_121_, v_unfold_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_unfold_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_125_, v_unfold_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_129_, lean_object* v_homo_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_129_, v_homo_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_homo_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_133_, v_homo_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_137_, lean_object* v_homoPred_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_137_, v_homoPred_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_homoPred_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_141_, v_homoPred_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_145_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
lean_ctor_set(v___x_151_, 4, v___x_149_);
lean_ctor_set(v___x_151_, 5, v___x_149_);
lean_ctor_set(v___x_151_, 6, v___x_149_);
lean_ctor_set(v___x_151_, 7, v___x_149_);
lean_ctor_set(v___x_151_, 8, v___x_149_);
lean_ctor_set(v___x_151_, 9, v___x_149_);
lean_ctor_set(v___x_151_, 10, v___x_149_);
lean_ctor_set(v___x_151_, 11, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((size_t)5ULL);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_unsigned_to_nat(32u);
v___x_158_ = lean_mk_empty_array_with_capacity(v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_156_);
lean_ctor_set(v___x_160_, 3, v___x_156_);
lean_ctor_set_usize(v___x_160_, 4, v___x_155_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_box(1);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_toCold_170_; lean_object* v_env_171_; lean_object* v_options_172_; uint8_t v___x_173_; lean_object* v_env_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_169_ = lean_st_ref_get(v___y_167_);
v_toCold_170_ = lean_ctor_get(v___y_166_, 0);
v_env_171_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_env_171_);
lean_dec(v___x_169_);
v_options_172_ = lean_ctor_get(v_toCold_170_, 2);
v___x_173_ = 0;
v_env_174_ = l_Lean_Environment_setRecordingDeps(v_env_171_, v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_172_);
v___x_177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_177_, 0, v_env_174_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
lean_ctor_set(v___x_177_, 3, v_options_172_);
v___x_178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_msgData_165_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_165_ = stack[0].m_obj;
lean_object* v___y_166_ = stack[1].m_obj;
lean_object* v___y_167_ = stack[2].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_185_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_ref_190_; lean_object* v___x_191_; lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_200_; 
v_ref_190_ = lean_ctor_get(v___y_187_, 2);
v___x_191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_186_, v___y_187_, v___y_188_);
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_200_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
lean_inc(v_ref_190_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_ref_190_);
lean_ctor_set(v___x_196_, 1, v_a_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 1);
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_186_ = stack[0].m_obj;
lean_object* v___y_187_ = stack[1].m_obj;
lean_object* v___y_188_ = stack[2].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_186_, v___y_187_, v___y_188_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_206_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_207_, lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_toCold_212_; lean_object* v_currRecDepth_213_; lean_object* v_ref_214_; uint16_t v_optionFlags_215_; uint8_t v_suppressElabErrors_216_; uint8_t v_isRecordingDeps_217_; lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_toCold_212_ = lean_ctor_get(v___y_209_, 0);
v_currRecDepth_213_ = lean_ctor_get(v___y_209_, 1);
v_ref_214_ = lean_ctor_get(v___y_209_, 2);
v_optionFlags_215_ = lean_ctor_get_uint16(v___y_209_, sizeof(void*)*3);
v_suppressElabErrors_216_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*3 + 2);
v_isRecordingDeps_217_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*3 + 3);
v_ref_218_ = l_Lean_replaceRef(v_ref_207_, v_ref_214_);
lean_inc(v_currRecDepth_213_);
lean_inc_ref(v_toCold_212_);
v___x_219_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_219_, 0, v_toCold_212_);
lean_ctor_set(v___x_219_, 1, v_currRecDepth_213_);
lean_ctor_set(v___x_219_, 2, v_ref_218_);
lean_ctor_set_uint16(v___x_219_, sizeof(void*)*3, v_optionFlags_215_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*3 + 2, v_suppressElabErrors_216_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*3 + 3, v_isRecordingDeps_217_);
v___x_220_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_208_, v___x_219_, v___y_210_);
lean_dec_ref_known(v___x_219_, 3);
return v___x_220_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_207_ = stack[0].m_obj;
lean_object* v_msg_208_ = stack[1].m_obj;
lean_object* v___y_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_207_, v_msg_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_222_, lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_222_, v_msg_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v_ref_222_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_410_);
v___x_415_ = l_Lean_Syntax_isOfKind(v_stx_410_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_416_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_417_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_420_, v_a_411_, v_a_412_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_Lean_Syntax_getArg(v_stx_410_, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_423_);
v___x_425_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_423_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_423_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_423_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_423_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_423_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_423_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_423_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_423_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_423_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_423_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_423_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_423_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_423_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_423_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_423_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_423_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_423_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_423_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_423_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_423_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_423_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
lean_inc(v___x_423_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_423_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v___x_423_);
v___x_470_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_471_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_474_, v_a_411_, v_a_412_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_stx_410_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = l_Lean_Syntax_getArg(v___x_423_, v___x_476_);
lean_dec(v___x_423_);
v___x_478_ = l_Lean_Syntax_isNatLit_x3f(v___x_477_);
if (lean_obj_tag(v___x_478_) == 1)
{
lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
lean_dec(v___x_477_);
v_val_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 5);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_val_479_);
v___x_484_ = v_reuseFailAlloc_486_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v___x_478_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__55, &l_Lean_Meta_Grind_getAttrKindCore___closed__55_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55);
v___x_489_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_477_, v___x_488_, v_a_411_, v_a_412_);
lean_dec(v___x_477_);
return v___x_489_;
}
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_490_ = lean_box(11);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_492_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_492_, 0, v___x_415_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_494_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_494_, 0, v___x_461_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_496_ = lean_box(9);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = l_Lean_Syntax_getArg(v___x_423_, v___x_498_);
lean_inc(v___x_499_);
v___x_500_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_422_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
lean_inc(v___x_499_);
v___x_501_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_499_);
lean_dec(v___x_423_);
v___x_502_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_503_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_506_, v_a_411_, v_a_412_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = l_Lean_Syntax_getArg(v___x_499_, v___x_422_);
lean_dec(v___x_499_);
v___x_509_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
lean_inc(v___x_508_);
v___x_510_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_423_);
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_514_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_517_, v_a_411_, v_a_412_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_unsigned_to_nat(2u);
v___x_520_ = l_Lean_Syntax_getArg(v___x_423_, v___x_519_);
lean_dec(v___x_423_);
lean_inc(v___x_520_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_520_, v___x_422_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Syntax_matchesNull(v___x_520_, v___x_498_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_524_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_527_, v_a_411_, v_a_412_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_stx_410_);
v___x_529_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_529_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_529_, 1, v___x_415_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_520_);
lean_dec(v_stx_410_);
v___x_531_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_531_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_531_, 1, v___x_510_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
lean_dec(v___x_508_);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = l_Lean_Syntax_getArg(v___x_423_, v___x_533_);
lean_dec(v___x_423_);
lean_inc(v___x_534_);
v___x_535_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_422_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_498_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_538_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_541_, v_a_411_, v_a_412_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_stx_410_);
v___x_543_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_543_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_543_, 1, v___x_415_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_534_);
lean_dec(v_stx_410_);
v___x_545_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_545_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_545_, 1, v___x_500_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
lean_dec(v___x_499_);
v___x_547_ = lean_unsigned_to_nat(2u);
v___x_548_ = l_Lean_Syntax_getArg(v___x_423_, v___x_547_);
lean_dec(v___x_423_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Syntax_matchesNull(v___x_548_, v___x_422_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Syntax_matchesNull(v___x_548_, v___x_498_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_552_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_555_, v_a_411_, v_a_412_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_stx_410_);
v___x_557_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_557_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_557_, 1, v___x_415_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_548_);
lean_dec(v_stx_410_);
v___x_559_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_559_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_559_, 1, v___x_457_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_561_ = lean_box(7);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_563_ = lean_box(6);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_565_ = lean_box(4);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_567_ = lean_box(2);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_569_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_569_, 0, v___x_415_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_571_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_571_, 0, v___x_445_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_573_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_573_, 0, v___x_415_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_582_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__64));
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(3u);
v___x_585_ = l_Lean_Syntax_getArg(v___x_423_, v___x_584_);
lean_dec(v___x_423_);
lean_inc(v___x_585_);
v___x_586_ = l_Lean_Syntax_matchesNull(v___x_585_, v___x_422_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_585_);
v___x_588_ = l_Lean_Syntax_matchesNull(v___x_585_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v___x_585_);
v___x_589_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_590_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_593_, v_a_411_, v_a_412_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = l_Lean_Syntax_getArg(v___x_585_, v___x_422_);
lean_dec(v___x_585_);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_597_ = l_Lean_Syntax_isOfKind(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_599_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_602_, v_a_411_, v_a_412_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_stx_410_);
v___x_604_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_604_, 0, v___x_415_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_585_);
lean_dec(v_stx_410_);
v___x_607_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_607_, 0, v___x_433_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_unsigned_to_nat(2u);
v___x_611_ = l_Lean_Syntax_getArg(v___x_423_, v___x_610_);
lean_dec(v___x_423_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_Syntax_matchesNull(v___x_611_, v___x_422_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_611_);
v___x_614_ = l_Lean_Syntax_matchesNull(v___x_611_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v___x_611_);
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_616_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_619_, v_a_411_, v_a_412_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Syntax_getArg(v___x_611_, v___x_422_);
lean_dec(v___x_611_);
v___x_622_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_623_ = l_Lean_Syntax_isOfKind(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_625_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_628_, v_a_411_, v_a_412_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_stx_410_);
v___x_630_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_630_, 0, v___x_415_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_611_);
lean_dec(v_stx_410_);
v___x_633_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_633_, 0, v___x_431_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = l_Lean_Syntax_getArg(v___x_423_, v___x_636_);
lean_dec(v___x_423_);
lean_inc(v___x_637_);
v___x_638_ = l_Lean_Syntax_matchesNull(v___x_637_, v___x_422_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
lean_inc(v___x_637_);
v___x_639_ = l_Lean_Syntax_matchesNull(v___x_637_, v___x_636_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v___x_637_);
v___x_640_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_641_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_644_, v_a_411_, v_a_412_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = l_Lean_Syntax_getArg(v___x_637_, v___x_422_);
lean_dec(v___x_637_);
v___x_647_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_648_ = l_Lean_Syntax_isOfKind(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_650_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_653_, v_a_411_, v_a_412_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_stx_410_);
v___x_655_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_655_, 0, v___x_415_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v___x_637_);
lean_dec(v_stx_410_);
v___x_658_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_658_, 0, v___x_429_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v___x_423_);
lean_dec(v_stx_410_);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = l_Lean_Syntax_getArg(v___x_423_, v___x_663_);
lean_dec(v___x_423_);
lean_inc(v___x_664_);
v___x_665_ = l_Lean_Syntax_matchesNull(v___x_664_, v___x_422_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
lean_inc(v___x_664_);
v___x_666_ = l_Lean_Syntax_matchesNull(v___x_664_, v___x_663_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___x_664_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_668_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_671_, v_a_411_, v_a_412_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = l_Lean_Syntax_getArg(v___x_664_, v___x_422_);
lean_dec(v___x_664_);
v___x_674_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_675_ = l_Lean_Syntax_isOfKind(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_677_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_680_, v_a_411_, v_a_412_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v_stx_410_);
v___x_682_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_682_, 0, v___x_415_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___x_664_);
lean_dec(v_stx_410_);
v___x_685_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_685_, 0, v___x_425_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = l_Lean_Syntax_getArg(v___x_423_, v___x_688_);
lean_dec(v___x_423_);
lean_inc(v___x_689_);
v___x_690_ = l_Lean_Syntax_matchesNull(v___x_689_, v___x_422_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
lean_inc(v___x_689_);
v___x_691_ = l_Lean_Syntax_matchesNull(v___x_689_, v___x_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___x_689_);
v___x_692_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_693_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_696_, v_a_411_, v_a_412_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = l_Lean_Syntax_getArg(v___x_689_, v___x_422_);
lean_dec(v___x_689_);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_700_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_702_ = l_Lean_MessageData_ofSyntax(v_stx_410_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_705_, v_a_411_, v_a_412_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_stx_410_);
v___x_707_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_707_, 0, v___x_415_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v___x_689_);
lean_dec(v_stx_410_);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__67));
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getAttrKindCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_410_ = stack[0].m_obj;
lean_object* v_a_411_ = stack[1].m_obj;
lean_object* v_a_412_ = stack[2].m_obj;
lean_object* v_res_712_;
v_res_712_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_410_, v_a_411_, v_a_412_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
return v_res_717_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_719_, v___y_720_, v___y_721_);
return v___x_723_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_719_ = stack[1].m_obj;
lean_object* v___y_720_ = stack[2].m_obj;
lean_object* v___y_721_ = stack[3].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_box(0), v_msg_719_, v___y_720_, v___y_721_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_725_, v_msg_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_730_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_731_, lean_object* v_ref_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_732_, v_msg_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_732_ = stack[1].m_obj;
lean_object* v_msg_733_ = stack[2].m_obj;
lean_object* v___y_734_ = stack[3].m_obj;
lean_object* v___y_735_ = stack[4].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_box(0), v_ref_732_, v_msg_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_739_, lean_object* v_ref_740_, lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_739_, v_ref_740_, v_msg_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v_ref_740_);
return v_res_745_;
}
}
lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = l_Lean_Syntax_getArg(v_stx_746_, v___x_750_);
v___x_752_ = l_Lean_Syntax_isNone(v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = l_Lean_Syntax_getArg(v___x_751_, v___x_753_);
lean_dec(v___x_751_);
v___x_755_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_754_, v_a_747_, v_a_748_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v___x_751_);
v___x_756_ = lean_box(3);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getAttrKindFromOpt_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_746_ = stack[0].m_obj;
lean_object* v_a_747_ = stack[1].m_obj;
lean_object* v_a_748_ = stack[2].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_746_, v_a_747_, v_a_748_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_stx_759_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_771_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_770_, v_a_767_, v_a_768_);
return v___x_771_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_767_ = stack[0].m_obj;
lean_object* v_a_768_ = stack[1].m_obj;
lean_object* v_res_772_;
v_res_772_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_767_, v_a_768_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_776_;
}
}
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_778_, v_a_779_);
return v___x_781_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_throwInvalidUsrModifier_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_778_ = stack[1].m_obj;
lean_object* v_a_779_ = stack[2].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_box(0), v_a_778_, v_a_779_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_787_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_792_, lean_object* v_b_793_, uint8_t v_kind_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_toCold_798_; lean_object* v_currNamespace_799_; lean_object* v___x_800_; lean_object* v_env_801_; lean_object* v_nextMacroScope_802_; lean_object* v_ngen_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_traceState_805_; lean_object* v_recordedDeps_806_; lean_object* v_messages_807_; lean_object* v_infoState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_821_; 
v_toCold_798_ = lean_ctor_get(v___y_795_, 0);
v_currNamespace_799_ = lean_ctor_get(v_toCold_798_, 4);
v___x_800_ = lean_st_ref_take(v___y_796_);
v_env_801_ = lean_ctor_get(v___x_800_, 0);
v_nextMacroScope_802_ = lean_ctor_get(v___x_800_, 1);
v_ngen_803_ = lean_ctor_get(v___x_800_, 2);
v_auxDeclNGen_804_ = lean_ctor_get(v___x_800_, 3);
v_traceState_805_ = lean_ctor_get(v___x_800_, 4);
v_recordedDeps_806_ = lean_ctor_get(v___x_800_, 6);
v_messages_807_ = lean_ctor_get(v___x_800_, 7);
v_infoState_808_ = lean_ctor_get(v___x_800_, 8);
v_snapshotTasks_809_ = lean_ctor_get(v___x_800_, 9);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_800_, 5);
lean_dec(v_unused_822_);
v___x_811_ = v___x_800_;
v_isShared_812_ = v_isSharedCheck_821_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_infoState_808_);
lean_inc(v_messages_807_);
lean_inc(v_recordedDeps_806_);
lean_inc(v_traceState_805_);
lean_inc(v_auxDeclNGen_804_);
lean_inc(v_ngen_803_);
lean_inc(v_nextMacroScope_802_);
lean_inc(v_env_801_);
lean_dec(v___x_800_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_821_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_813_ = lean_box(0);
lean_inc(v_currNamespace_799_);
v___x_814_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_801_, v_ext_792_, v_b_793_, v_kind_794_, v_currNamespace_799_);
v___x_815_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v___x_815_);
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_nextMacroScope_802_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_ngen_803_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_traceState_805_);
lean_ctor_set(v_reuseFailAlloc_820_, 5, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 6, v_recordedDeps_806_);
lean_ctor_set(v_reuseFailAlloc_820_, 7, v_messages_807_);
lean_ctor_set(v_reuseFailAlloc_820_, 8, v_infoState_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 9, v_snapshotTasks_809_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_st_ref_put(v___y_796_, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_813_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_792_ = stack[0].m_obj;
lean_object* v_b_793_ = stack[1].m_obj;
uint8_t v_kind_794_ = stack[2].m_num;
lean_object* v___y_795_ = stack[3].m_obj;
lean_object* v___y_796_ = stack[4].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_792_, v_b_793_, v_kind_794_, v___y_795_, v___y_796_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_824_, lean_object* v_b_825_, lean_object* v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v_kind_boxed_830_; lean_object* v_res_831_; 
v_kind_boxed_830_ = lean_unbox(v_kind_826_);
v_res_831_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_824_, v_b_825_, v_kind_boxed_830_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_831_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_00_u03c3_834_, lean_object* v_ext_835_, lean_object* v_b_836_, uint8_t v_kind_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_835_, v_b_836_, v_kind_837_, v___y_838_, v___y_839_);
return v___x_841_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_835_ = stack[3].m_obj;
lean_object* v_b_836_ = stack[4].m_obj;
uint8_t v_kind_837_ = stack[5].m_num;
lean_object* v___y_838_ = stack[6].m_obj;
lean_object* v___y_839_ = stack[7].m_obj;
lean_object* v_res_842_;
v_res_842_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_box(0), lean_box(0), lean_box(0), v_ext_835_, v_b_836_, v_kind_837_, v___y_838_, v___y_839_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_00_u03c3_845_, lean_object* v_ext_846_, lean_object* v_b_847_, lean_object* v_kind_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_kind_boxed_852_; lean_object* v_res_853_; 
v_kind_boxed_852_ = lean_unbox(v_kind_848_);
v_res_853_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_843_, v_00_u03b2_844_, v_00_u03c3_845_, v_ext_846_, v_b_847_, v_kind_boxed_852_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_853_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_854_, lean_object* v_declName_855_, uint8_t v_eager_856_, uint8_t v_attrKind_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
lean_inc(v_declName_855_);
v___x_861_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_855_, v_eager_856_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_862_, 0, v_declName_855_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v_eager_856_);
v___x_863_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_854_, v___x_862_, v_attrKind_857_, v_a_858_, v_a_859_);
return v___x_863_;
}
else
{
lean_dec(v_declName_855_);
lean_dec_ref(v_ext_854_);
return v___x_861_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_854_ = stack[0].m_obj;
lean_object* v_declName_855_ = stack[1].m_obj;
uint8_t v_eager_856_ = stack[2].m_num;
uint8_t v_attrKind_857_ = stack[3].m_num;
lean_object* v_a_858_ = stack[4].m_obj;
lean_object* v_a_859_ = stack[5].m_obj;
lean_object* v_res_864_;
v_res_864_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_854_, v_declName_855_, v_eager_856_, v_attrKind_857_, v_a_858_, v_a_859_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_865_, lean_object* v_declName_866_, lean_object* v_eager_867_, lean_object* v_attrKind_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
uint8_t v_eager_boxed_872_; uint8_t v_attrKind_boxed_873_; lean_object* v_res_874_; 
v_eager_boxed_872_ = lean_unbox(v_eager_867_);
v_attrKind_boxed_873_ = lean_unbox(v_attrKind_868_);
v_res_874_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_865_, v_declName_866_, v_eager_boxed_872_, v_attrKind_boxed_873_, v_a_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
return v_res_874_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_875_, lean_object* v_declName_876_, uint8_t v_attrKind_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; 
lean_inc(v_declName_876_);
v___x_881_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_876_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_881_, 0);
lean_dec(v_unused_890_);
v___x_883_ = v___x_881_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_881_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_declName_876_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_declName_876_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_875_, v___x_886_, v_attrKind_877_, v_a_878_, v_a_879_);
return v___x_887_;
}
}
}
else
{
lean_dec(v_declName_876_);
lean_dec_ref(v_ext_875_);
return v___x_881_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_875_ = stack[0].m_obj;
lean_object* v_declName_876_ = stack[1].m_obj;
uint8_t v_attrKind_877_ = stack[2].m_num;
lean_object* v_a_878_ = stack[3].m_obj;
lean_object* v_a_879_ = stack[4].m_obj;
lean_object* v_res_891_;
v_res_891_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_875_, v_declName_876_, v_attrKind_877_, v_a_878_, v_a_879_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_892_, lean_object* v_declName_893_, lean_object* v_attrKind_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
uint8_t v_attrKind_boxed_898_; lean_object* v_res_899_; 
v_attrKind_boxed_898_ = lean_unbox(v_attrKind_894_);
v_res_899_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_892_, v_declName_893_, v_attrKind_boxed_898_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_899_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_900_, lean_object* v_declName_901_, uint8_t v_attrKind_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_declName_901_);
v___x_907_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_900_, v___x_906_, v_attrKind_902_, v_a_903_, v_a_904_);
return v___x_907_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_900_ = stack[0].m_obj;
lean_object* v_declName_901_ = stack[1].m_obj;
uint8_t v_attrKind_902_ = stack[2].m_num;
lean_object* v_a_903_ = stack[3].m_obj;
lean_object* v_a_904_ = stack[4].m_obj;
lean_object* v_res_908_;
v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_900_, v_declName_901_, v_attrKind_902_, v_a_903_, v_a_904_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_909_, lean_object* v_declName_910_, lean_object* v_attrKind_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
uint8_t v_attrKind_boxed_915_; lean_object* v_res_916_; 
v_attrKind_boxed_915_ = lean_unbox(v_attrKind_911_);
v_res_916_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_909_, v_declName_910_, v_attrKind_boxed_915_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_917_, lean_object* v_s_918_){
_start:
{
lean_object* v_casesTypes_919_; lean_object* v_funCC_920_; lean_object* v_ematch_921_; lean_object* v_inj_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_casesTypes_919_ = lean_ctor_get(v_s_918_, 0);
v_funCC_920_ = lean_ctor_get(v_s_918_, 2);
v_ematch_921_ = lean_ctor_get(v_s_918_, 3);
v_inj_922_ = lean_ctor_get(v_s_918_, 4);
v_isSharedCheck_929_ = !lean_is_exclusive(v_s_918_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_s_918_, 1);
lean_dec(v_unused_930_);
v___x_924_ = v_s_918_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_inj_922_);
lean_inc(v_ematch_921_);
lean_inc(v_funCC_920_);
lean_inc(v_casesTypes_919_);
lean_dec(v_s_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v_a_917_);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_casesTypes_919_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_funCC_920_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_ematch_921_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_inj_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_931_, lean_object* v_declName_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_ext_938_; lean_object* v_toEnvExtension_939_; lean_object* v_env_940_; lean_object* v_asyncMode_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v_extThms_944_; lean_object* v___x_945_; 
v___x_936_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_937_ = lean_st_ref_get(v_a_934_);
v_ext_938_ = lean_ctor_get(v_ext_931_, 1);
v_toEnvExtension_939_ = lean_ctor_get(v_ext_938_, 0);
v_env_940_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_940_);
lean_dec(v___x_937_);
v_asyncMode_941_ = lean_ctor_get(v_toEnvExtension_939_, 2);
v___x_942_ = 0;
v___x_943_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_936_, v_ext_931_, v_env_940_, v_asyncMode_941_, v___x_942_);
v_extThms_944_ = lean_ctor_get(v___x_943_, 1);
lean_inc_ref(v_extThms_944_);
lean_dec(v___x_943_);
v___x_945_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_944_, v_declName_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_976_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_976_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_976_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_976_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v_env_952_; lean_object* v_nextMacroScope_953_; lean_object* v_ngen_954_; lean_object* v_auxDeclNGen_955_; lean_object* v_traceState_956_; lean_object* v_recordedDeps_957_; lean_object* v_messages_958_; lean_object* v_infoState_959_; lean_object* v_snapshotTasks_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_974_; 
v___f_950_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_950_, 0, v_a_946_);
v___x_951_ = lean_st_ref_take(v_a_934_);
v_env_952_ = lean_ctor_get(v___x_951_, 0);
v_nextMacroScope_953_ = lean_ctor_get(v___x_951_, 1);
v_ngen_954_ = lean_ctor_get(v___x_951_, 2);
v_auxDeclNGen_955_ = lean_ctor_get(v___x_951_, 3);
v_traceState_956_ = lean_ctor_get(v___x_951_, 4);
v_recordedDeps_957_ = lean_ctor_get(v___x_951_, 6);
v_messages_958_ = lean_ctor_get(v___x_951_, 7);
v_infoState_959_ = lean_ctor_get(v___x_951_, 8);
v_snapshotTasks_960_ = lean_ctor_get(v___x_951_, 9);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_951_, 5);
lean_dec(v_unused_975_);
v___x_962_ = v___x_951_;
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_snapshotTasks_960_);
lean_inc(v_infoState_959_);
lean_inc(v_messages_958_);
lean_inc(v_recordedDeps_957_);
lean_inc(v_traceState_956_);
lean_inc(v_auxDeclNGen_955_);
lean_inc(v_ngen_954_);
lean_inc(v_nextMacroScope_953_);
lean_inc(v_env_952_);
lean_dec(v___x_951_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_974_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_964_ = lean_box(0);
v___x_965_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_931_, v_env_952_, v___f_950_);
v___x_966_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 5, v___x_966_);
lean_ctor_set(v___x_962_, 0, v___x_965_);
v___x_968_ = v___x_962_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_nextMacroScope_953_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_ngen_954_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v_auxDeclNGen_955_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v_traceState_956_);
lean_ctor_set(v_reuseFailAlloc_973_, 5, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_973_, 6, v_recordedDeps_957_);
lean_ctor_set(v_reuseFailAlloc_973_, 7, v_messages_958_);
lean_ctor_set(v_reuseFailAlloc_973_, 8, v_infoState_959_);
lean_ctor_set(v_reuseFailAlloc_973_, 9, v_snapshotTasks_960_);
v___x_968_ = v_reuseFailAlloc_973_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_st_ref_put(v_a_934_, v___x_968_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_964_);
v___x_971_ = v___x_948_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_964_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v_ext_931_);
v_a_977_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_945_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_945_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_931_ = stack[0].m_obj;
lean_object* v_declName_932_ = stack[1].m_obj;
lean_object* v_a_933_ = stack[2].m_obj;
lean_object* v_a_934_ = stack[3].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_931_, v_declName_932_, v_a_933_, v_a_934_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_986_, lean_object* v_declName_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_986_, v_declName_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_992_, lean_object* v_s_993_){
_start:
{
lean_object* v_extThms_994_; lean_object* v_funCC_995_; lean_object* v_ematch_996_; lean_object* v_inj_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_extThms_994_ = lean_ctor_get(v_s_993_, 1);
v_funCC_995_ = lean_ctor_get(v_s_993_, 2);
v_ematch_996_ = lean_ctor_get(v_s_993_, 3);
v_inj_997_ = lean_ctor_get(v_s_993_, 4);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_s_993_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_s_993_, 0);
lean_dec(v_unused_1005_);
v___x_999_ = v_s_993_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_inj_997_);
lean_inc(v_ematch_996_);
lean_inc(v_funCC_995_);
lean_inc(v_extThms_994_);
lean_dec(v_s_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_a_992_);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_992_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_extThms_994_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_funCC_995_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_ematch_996_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_inj_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_1006_, lean_object* v_declName_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_1007_);
v___x_1012_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1013_; lean_object* v_ext_1014_; lean_object* v_toEnvExtension_1015_; lean_object* v_env_1016_; lean_object* v_asyncMode_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v_casesTypes_1020_; lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1012_, 1);
v___x_1013_ = lean_st_ref_get(v_a_1009_);
v_ext_1014_ = lean_ctor_get(v_ext_1006_, 1);
v_toEnvExtension_1015_ = lean_ctor_get(v_ext_1014_, 0);
v_env_1016_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_env_1016_);
lean_dec(v___x_1013_);
v_asyncMode_1017_ = lean_ctor_get(v_toEnvExtension_1015_, 2);
v___x_1018_ = 0;
v___x_1019_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1011_, v_ext_1006_, v_env_1016_, v_asyncMode_1017_, v___x_1018_);
v_casesTypes_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_casesTypes_1020_);
lean_dec(v___x_1019_);
v___x_1021_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_1020_, v_declName_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1052_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1052_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1052_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v_env_1028_; lean_object* v_nextMacroScope_1029_; lean_object* v_ngen_1030_; lean_object* v_auxDeclNGen_1031_; lean_object* v_traceState_1032_; lean_object* v_recordedDeps_1033_; lean_object* v_messages_1034_; lean_object* v_infoState_1035_; lean_object* v_snapshotTasks_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1050_; 
v___f_1026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1026_, 0, v_a_1022_);
v___x_1027_ = lean_st_ref_take(v_a_1009_);
v_env_1028_ = lean_ctor_get(v___x_1027_, 0);
v_nextMacroScope_1029_ = lean_ctor_get(v___x_1027_, 1);
v_ngen_1030_ = lean_ctor_get(v___x_1027_, 2);
v_auxDeclNGen_1031_ = lean_ctor_get(v___x_1027_, 3);
v_traceState_1032_ = lean_ctor_get(v___x_1027_, 4);
v_recordedDeps_1033_ = lean_ctor_get(v___x_1027_, 6);
v_messages_1034_ = lean_ctor_get(v___x_1027_, 7);
v_infoState_1035_ = lean_ctor_get(v___x_1027_, 8);
v_snapshotTasks_1036_ = lean_ctor_get(v___x_1027_, 9);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1027_, 5);
lean_dec(v_unused_1051_);
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snapshotTasks_1036_);
lean_inc(v_infoState_1035_);
lean_inc(v_messages_1034_);
lean_inc(v_recordedDeps_1033_);
lean_inc(v_traceState_1032_);
lean_inc(v_auxDeclNGen_1031_);
lean_inc(v_ngen_1030_);
lean_inc(v_nextMacroScope_1029_);
lean_inc(v_env_1028_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1050_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1006_, v_env_1028_, v___f_1026_);
v___x_1042_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 5, v___x_1042_);
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_nextMacroScope_1029_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_ngen_1030_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_auxDeclNGen_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_traceState_1032_);
lean_ctor_set(v_reuseFailAlloc_1049_, 5, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 6, v_recordedDeps_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 7, v_messages_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 8, v_infoState_1035_);
lean_ctor_set(v_reuseFailAlloc_1049_, 9, v_snapshotTasks_1036_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_st_ref_put(v_a_1009_, v___x_1044_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1040_);
v___x_1047_ = v___x_1024_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1040_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_ext_1006_);
v_a_1053_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1021_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1021_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_dec(v_declName_1007_);
lean_dec_ref(v_ext_1006_);
return v___x_1012_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1006_ = stack[0].m_obj;
lean_object* v_declName_1007_ = stack[1].m_obj;
lean_object* v_a_1008_ = stack[2].m_obj;
lean_object* v_a_1009_ = stack[3].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1006_, v_declName_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1062_, lean_object* v_declName_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1062_, v_declName_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1068_, lean_object* v_s_1069_){
_start:
{
lean_object* v_casesTypes_1070_; lean_object* v_extThms_1071_; lean_object* v_ematch_1072_; lean_object* v_inj_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_casesTypes_1070_ = lean_ctor_get(v_s_1069_, 0);
v_extThms_1071_ = lean_ctor_get(v_s_1069_, 1);
v_ematch_1072_ = lean_ctor_get(v_s_1069_, 3);
v_inj_1073_ = lean_ctor_get(v_s_1069_, 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_s_1069_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_s_1069_, 2);
lean_dec(v_unused_1081_);
v___x_1075_ = v_s_1069_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_inj_1073_);
lean_inc(v_ematch_1072_);
lean_inc(v_extThms_1071_);
lean_inc(v_casesTypes_1070_);
lean_dec(v_s_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 2, v___x_1068_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_casesTypes_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_extThms_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_ematch_1072_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_inj_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1082_, lean_object* v_t_1083_){
_start:
{
if (lean_obj_tag(v_t_1083_) == 0)
{
lean_object* v_k_1084_; lean_object* v_v_1085_; lean_object* v_l_1086_; lean_object* v_r_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1741_; 
v_k_1084_ = lean_ctor_get(v_t_1083_, 1);
v_v_1085_ = lean_ctor_get(v_t_1083_, 2);
v_l_1086_ = lean_ctor_get(v_t_1083_, 3);
v_r_1087_ = lean_ctor_get(v_t_1083_, 4);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_t_1083_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_t_1083_, 0);
lean_dec(v_unused_1742_);
v___x_1089_ = v_t_1083_;
v_isShared_1090_ = v_isSharedCheck_1741_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_r_1087_);
lean_inc(v_l_1086_);
lean_inc(v_v_1085_);
lean_inc(v_k_1084_);
lean_dec(v_t_1083_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1741_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1082_, v_k_1084_);
switch(v___x_1091_)
{
case 0:
{
lean_object* v_impl_1092_; lean_object* v___x_1093_; 
v_impl_1092_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1082_, v_l_1086_);
v___x_1093_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1092_) == 0)
{
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_size_1094_; lean_object* v_size_1095_; lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_l_1098_; lean_object* v_r_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_size_1094_ = lean_ctor_get(v_impl_1092_, 0);
v_size_1095_ = lean_ctor_get(v_r_1087_, 0);
v_k_1096_ = lean_ctor_get(v_r_1087_, 1);
v_v_1097_ = lean_ctor_get(v_r_1087_, 2);
v_l_1098_ = lean_ctor_get(v_r_1087_, 3);
lean_inc(v_l_1098_);
v_r_1099_ = lean_ctor_get(v_r_1087_, 4);
v___x_1100_ = lean_unsigned_to_nat(3u);
v___x_1101_ = lean_nat_mul(v___x_1100_, v_size_1094_);
v___x_1102_ = lean_nat_dec_lt(v___x_1101_, v_size_1095_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v_l_1098_);
v___x_1103_ = lean_nat_add(v___x_1093_, v_size_1094_);
v___x_1104_ = lean_nat_add(v___x_1103_, v_size_1095_);
lean_dec(v___x_1103_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 3, v_impl_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1104_);
v___x_1106_ = v___x_1089_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_r_1087_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1171_; 
lean_inc(v_r_1099_);
lean_inc(v_v_1097_);
lean_inc(v_k_1096_);
lean_inc(v_size_1095_);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1172_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_r_1087_, 2);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_r_1087_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1176_);
v___x_1109_ = v_r_1087_;
v_isShared_1110_ = v_isSharedCheck_1171_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_r_1087_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1171_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_size_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v_r_1115_; lean_object* v_size_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_size_1111_ = lean_ctor_get(v_l_1098_, 0);
v_k_1112_ = lean_ctor_get(v_l_1098_, 1);
v_v_1113_ = lean_ctor_get(v_l_1098_, 2);
v_l_1114_ = lean_ctor_get(v_l_1098_, 3);
v_r_1115_ = lean_ctor_get(v_l_1098_, 4);
v_size_1116_ = lean_ctor_get(v_r_1099_, 0);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_nat_mul(v___x_1117_, v_size_1116_);
v___x_1119_ = lean_nat_dec_lt(v_size_1111_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1147_; 
lean_inc(v_r_1115_);
lean_inc(v_l_1114_);
lean_inc(v_v_1113_);
lean_inc(v_k_1112_);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_l_1098_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_l_1098_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_l_1098_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_l_1098_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_l_1098_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_l_1098_, 0);
lean_dec(v_unused_1152_);
v___x_1121_ = v_l_1098_;
v_isShared_1122_ = v_isSharedCheck_1147_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v_l_1098_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1147_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1137_; 
v___x_1123_ = lean_nat_add(v___x_1093_, v_size_1094_);
v___x_1124_ = lean_nat_add(v___x_1123_, v_size_1095_);
lean_dec(v_size_1095_);
if (lean_obj_tag(v_l_1114_) == 0)
{
lean_object* v_size_1145_; 
v_size_1145_ = lean_ctor_get(v_l_1114_, 0);
lean_inc(v_size_1145_);
v___y_1137_ = v_size_1145_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___y_1137_ = v___x_1146_;
goto v___jp_1136_;
}
v___jp_1125_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_nat_add(v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec(v___y_1127_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v_r_1099_);
lean_ctor_set(v___x_1121_, 3, v_r_1115_);
lean_ctor_set(v___x_1121_, 2, v_v_1097_);
lean_ctor_set(v___x_1121_, 1, v_k_1096_);
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_r_1115_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_1099_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v___x_1131_);
lean_ctor_set(v___x_1109_, 3, v___y_1126_);
lean_ctor_set(v___x_1109_, 2, v_v_1113_);
lean_ctor_set(v___x_1109_, 1, v_k_1112_);
lean_ctor_set(v___x_1109_, 0, v___x_1124_);
v___x_1133_ = v___x_1109_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___y_1126_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_nat_add(v___x_1123_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec(v___x_1123_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1114_);
lean_ctor_set(v___x_1089_, 3, v_impl_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1138_);
v___x_1140_ = v___x_1089_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_l_1114_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_nat_add(v___x_1093_, v_size_1116_);
if (lean_obj_tag(v_r_1115_) == 0)
{
lean_object* v_size_1142_; 
v_size_1142_ = lean_ctor_get(v_r_1115_, 0);
lean_inc(v_size_1142_);
v___y_1126_ = v___x_1140_;
v___y_1127_ = v___x_1141_;
v___y_1128_ = v_size_1142_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___y_1126_ = v___x_1140_;
v___y_1127_ = v___x_1141_;
v___y_1128_ = v___x_1143_;
goto v___jp_1125_;
}
}
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_del_object(v___x_1089_);
v___x_1153_ = lean_nat_add(v___x_1093_, v_size_1094_);
v___x_1154_ = lean_nat_add(v___x_1153_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1155_ = lean_nat_add(v___x_1153_, v_size_1111_);
lean_dec(v___x_1153_);
lean_inc_ref(v_impl_1092_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v_l_1098_);
lean_ctor_set(v___x_1109_, 3, v_impl_1092_);
lean_ctor_set(v___x_1109_, 2, v_v_1085_);
lean_ctor_set(v___x_1109_, 1, v_k_1084_);
lean_ctor_set(v___x_1109_, 0, v___x_1155_);
v___x_1157_ = v___x_1109_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_l_1098_);
v___x_1157_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_isSharedCheck_1164_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1165_ = lean_ctor_get(v_impl_1092_, 4);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_impl_1092_, 2);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_impl_1092_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1169_);
v___x_1159_ = v_impl_1092_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_impl_1092_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_r_1099_);
lean_ctor_set(v___x_1159_, 3, v___x_1157_);
lean_ctor_set(v___x_1159_, 2, v_v_1097_);
lean_ctor_set(v___x_1159_, 1, v_k_1096_);
lean_ctor_set(v___x_1159_, 0, v___x_1154_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_r_1099_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v_size_1177_ = lean_ctor_get(v_impl_1092_, 0);
v___x_1178_ = lean_nat_add(v___x_1093_, v_size_1177_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 3, v_impl_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1178_);
v___x_1180_ = v___x_1089_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_r_1087_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_l_1182_; 
v_l_1182_ = lean_ctor_get(v_r_1087_, 3);
lean_inc(v_l_1182_);
if (lean_obj_tag(v_l_1182_) == 0)
{
lean_object* v_r_1183_; 
v_r_1183_ = lean_ctor_get(v_r_1087_, 4);
lean_inc(v_r_1183_);
if (lean_obj_tag(v_r_1183_) == 0)
{
lean_object* v_size_1184_; lean_object* v_k_1185_; lean_object* v_v_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1199_; 
v_size_1184_ = lean_ctor_get(v_r_1087_, 0);
v_k_1185_ = lean_ctor_get(v_r_1087_, 1);
v_v_1186_ = lean_ctor_get(v_r_1087_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1200_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1201_);
v___x_1188_ = v_r_1087_;
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_v_1186_);
lean_inc(v_k_1185_);
lean_inc(v_size_1184_);
lean_dec(v_r_1087_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_size_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_size_1190_ = lean_ctor_get(v_l_1182_, 0);
v___x_1191_ = lean_nat_add(v___x_1093_, v_size_1184_);
lean_dec(v_size_1184_);
v___x_1192_ = lean_nat_add(v___x_1093_, v_size_1190_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 4, v_l_1182_);
lean_ctor_set(v___x_1188_, 3, v_impl_1092_);
lean_ctor_set(v___x_1188_, 2, v_v_1085_);
lean_ctor_set(v___x_1188_, 1, v_k_1084_);
lean_ctor_set(v___x_1188_, 0, v___x_1192_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_l_1182_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_r_1183_);
lean_ctor_set(v___x_1089_, 3, v___x_1194_);
lean_ctor_set(v___x_1089_, 2, v_v_1186_);
lean_ctor_set(v___x_1089_, 1, v_k_1185_);
lean_ctor_set(v___x_1089_, 0, v___x_1191_);
v___x_1196_ = v___x_1089_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1186_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_r_1183_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1226_; 
v_k_1202_ = lean_ctor_get(v_r_1087_, 1);
v_v_1203_ = lean_ctor_get(v_r_1087_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1227_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1229_);
v___x_1205_ = v_r_1087_;
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_dec(v_r_1087_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_k_1207_; lean_object* v_v_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1222_; 
v_k_1207_ = lean_ctor_get(v_l_1182_, 1);
v_v_1208_ = lean_ctor_get(v_l_1182_, 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_l_1182_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; lean_object* v_unused_1225_; 
v_unused_1223_ = lean_ctor_get(v_l_1182_, 4);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_l_1182_, 3);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_l_1182_, 0);
lean_dec(v_unused_1225_);
v___x_1210_ = v_l_1182_;
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
lean_dec(v_l_1182_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_unsigned_to_nat(3u);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v_r_1183_);
lean_ctor_set(v___x_1210_, 3, v_r_1183_);
lean_ctor_set(v___x_1210_, 2, v_v_1085_);
lean_ctor_set(v___x_1210_, 1, v_k_1084_);
lean_ctor_set(v___x_1210_, 0, v___x_1093_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_r_1183_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_r_1183_);
v___x_1214_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 3, v_r_1183_);
lean_ctor_set(v___x_1205_, 0, v___x_1093_);
v___x_1216_ = v___x_1205_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_r_1183_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_r_1183_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1216_);
lean_ctor_set(v___x_1089_, 3, v___x_1214_);
lean_ctor_set(v___x_1089_, 2, v_v_1208_);
lean_ctor_set(v___x_1089_, 1, v_k_1207_);
lean_ctor_set(v___x_1089_, 0, v___x_1212_);
v___x_1218_ = v___x_1089_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1230_; 
v_r_1230_ = lean_ctor_get(v_r_1087_, 4);
lean_inc(v_r_1230_);
if (lean_obj_tag(v_r_1230_) == 0)
{
lean_object* v_k_1231_; lean_object* v_v_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v_k_1231_ = lean_ctor_get(v_r_1087_, 1);
v_v_1232_ = lean_ctor_get(v_r_1087_, 2);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; lean_object* v_unused_1246_; 
v_unused_1244_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1246_);
v___x_1234_ = v_r_1087_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_v_1232_);
lean_inc(v_k_1231_);
lean_dec(v_r_1087_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_unsigned_to_nat(3u);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v_l_1182_);
lean_ctor_set(v___x_1234_, 2, v_v_1085_);
lean_ctor_set(v___x_1234_, 1, v_k_1084_);
lean_ctor_set(v___x_1234_, 0, v___x_1093_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_l_1182_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_l_1182_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_r_1230_);
lean_ctor_set(v___x_1089_, 3, v___x_1238_);
lean_ctor_set(v___x_1089_, 2, v_v_1232_);
lean_ctor_set(v___x_1089_, 1, v_k_1231_);
lean_ctor_set(v___x_1089_, 0, v___x_1236_);
v___x_1240_ = v___x_1089_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1232_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1230_);
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
else
{
lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1260_; 
v_size_1247_ = lean_ctor_get(v_r_1087_, 0);
v_k_1248_ = lean_ctor_get(v_r_1087_, 1);
v_v_1249_ = lean_ctor_get(v_r_1087_, 2);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; lean_object* v_unused_1262_; 
v_unused_1261_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1261_);
v_unused_1262_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1262_);
v___x_1251_ = v_r_1087_;
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
lean_inc(v_size_1247_);
lean_dec(v_r_1087_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 3, v_r_1230_);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_size_1247_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_r_1230_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_r_1230_);
v___x_1254_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_unsigned_to_nat(2u);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1254_);
lean_ctor_set(v___x_1089_, 3, v_r_1230_);
lean_ctor_set(v___x_1089_, 0, v___x_1255_);
v___x_1257_ = v___x_1089_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_r_1230_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v___x_1254_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
else
{
lean_object* v___x_1264_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 3, v_r_1087_);
lean_ctor_set(v___x_1089_, 0, v___x_1093_);
v___x_1264_ = v___x_1089_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_r_1087_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_r_1087_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1089_);
lean_dec(v_v_1085_);
lean_dec(v_k_1084_);
if (lean_obj_tag(v_l_1086_) == 0)
{
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v_size_1271_; lean_object* v_k_1272_; lean_object* v_v_1273_; lean_object* v_l_1274_; lean_object* v_r_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_size_1266_ = lean_ctor_get(v_l_1086_, 0);
v_k_1267_ = lean_ctor_get(v_l_1086_, 1);
v_v_1268_ = lean_ctor_get(v_l_1086_, 2);
v_l_1269_ = lean_ctor_get(v_l_1086_, 3);
v_r_1270_ = lean_ctor_get(v_l_1086_, 4);
lean_inc(v_r_1270_);
v_size_1271_ = lean_ctor_get(v_r_1087_, 0);
v_k_1272_ = lean_ctor_get(v_r_1087_, 1);
v_v_1273_ = lean_ctor_get(v_r_1087_, 2);
v_l_1274_ = lean_ctor_get(v_r_1087_, 3);
lean_inc(v_l_1274_);
v_r_1275_ = lean_ctor_get(v_r_1087_, 4);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_dec_lt(v_size_1266_, v_size_1271_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1413_; 
lean_inc(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1414_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1418_);
v___x_1279_ = v_l_1086_;
v_isShared_1280_ = v_isSharedCheck_1413_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v_l_1086_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1413_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v_tree_1282_; 
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1267_, v_v_1268_, v_l_1269_, v_r_1270_);
v_tree_1282_ = lean_ctor_get(v___x_1281_, 2);
if (lean_obj_tag(v_tree_1282_) == 0)
{
lean_object* v_k_1283_; lean_object* v_v_1284_; lean_object* v_size_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
lean_inc_ref(v_tree_1282_);
v_k_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_k_1283_);
v_v_1284_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_v_1284_);
lean_dec_ref(v___x_1281_);
v_size_1285_ = lean_ctor_get(v_tree_1282_, 0);
v___x_1286_ = lean_unsigned_to_nat(3u);
v___x_1287_ = lean_nat_mul(v___x_1286_, v_size_1285_);
v___x_1288_ = lean_nat_dec_lt(v___x_1287_, v_size_1271_);
lean_dec(v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
lean_dec(v_l_1274_);
v___x_1289_ = lean_nat_add(v___x_1276_, v_size_1285_);
v___x_1290_ = lean_nat_add(v___x_1289_, v_size_1271_);
lean_dec(v___x_1289_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_r_1087_);
lean_ctor_set(v___x_1279_, 3, v_tree_1282_);
lean_ctor_set(v___x_1279_, 2, v_v_1284_);
lean_ctor_set(v___x_1279_, 1, v_k_1283_);
lean_ctor_set(v___x_1279_, 0, v___x_1290_);
v___x_1292_ = v___x_1279_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1283_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1284_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_tree_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_r_1087_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1348_; 
lean_inc(v_r_1275_);
lean_inc(v_v_1273_);
lean_inc(v_k_1272_);
lean_inc(v_size_1271_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1349_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_r_1087_, 2);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_r_1087_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1353_);
v___x_1295_ = v_r_1087_;
v_isShared_1296_ = v_isSharedCheck_1348_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_r_1087_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1348_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_l_1300_; lean_object* v_r_1301_; lean_object* v_size_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_size_1297_ = lean_ctor_get(v_l_1274_, 0);
v_k_1298_ = lean_ctor_get(v_l_1274_, 1);
v_v_1299_ = lean_ctor_get(v_l_1274_, 2);
v_l_1300_ = lean_ctor_get(v_l_1274_, 3);
v_r_1301_ = lean_ctor_get(v_l_1274_, 4);
v_size_1302_ = lean_ctor_get(v_r_1275_, 0);
v___x_1303_ = lean_unsigned_to_nat(2u);
v___x_1304_ = lean_nat_mul(v___x_1303_, v_size_1302_);
v___x_1305_ = lean_nat_dec_lt(v_size_1297_, v___x_1304_);
lean_dec(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1333_; 
lean_inc(v_r_1301_);
lean_inc(v_l_1300_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_l_1274_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1334_ = lean_ctor_get(v_l_1274_, 4);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_l_1274_, 3);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v_l_1274_, 2);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_l_1274_, 1);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_l_1274_, 0);
lean_dec(v_unused_1338_);
v___x_1307_ = v_l_1274_;
v_isShared_1308_ = v_isSharedCheck_1333_;
goto v_resetjp_1306_;
}
else
{
lean_dec(v_l_1274_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1333_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1323_; 
v___x_1309_ = lean_nat_add(v___x_1276_, v_size_1285_);
v___x_1310_ = lean_nat_add(v___x_1309_, v_size_1271_);
lean_dec(v_size_1271_);
if (lean_obj_tag(v_l_1300_) == 0)
{
lean_object* v_size_1331_; 
v_size_1331_ = lean_ctor_get(v_l_1300_, 0);
lean_inc(v_size_1331_);
v___y_1323_ = v_size_1331_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___y_1323_ = v___x_1332_;
goto v___jp_1322_;
}
v___jp_1311_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = lean_nat_add(v___y_1312_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec(v___y_1312_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 4, v_r_1275_);
lean_ctor_set(v___x_1307_, 3, v_r_1301_);
lean_ctor_set(v___x_1307_, 2, v_v_1273_);
lean_ctor_set(v___x_1307_, 1, v_k_1272_);
lean_ctor_set(v___x_1307_, 0, v___x_1315_);
v___x_1317_ = v___x_1307_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_r_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_r_1275_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 4, v___x_1317_);
lean_ctor_set(v___x_1295_, 3, v___y_1313_);
lean_ctor_set(v___x_1295_, 2, v_v_1299_);
lean_ctor_set(v___x_1295_, 1, v_k_1298_);
lean_ctor_set(v___x_1295_, 0, v___x_1310_);
v___x_1319_ = v___x_1295_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v___y_1313_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_nat_add(v___x_1309_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec(v___x_1309_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_l_1300_);
lean_ctor_set(v___x_1279_, 3, v_tree_1282_);
lean_ctor_set(v___x_1279_, 2, v_v_1284_);
lean_ctor_set(v___x_1279_, 1, v_k_1283_);
lean_ctor_set(v___x_1279_, 0, v___x_1324_);
v___x_1326_ = v___x_1279_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1283_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1284_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_tree_1282_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_l_1300_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_nat_add(v___x_1276_, v_size_1302_);
if (lean_obj_tag(v_r_1301_) == 0)
{
lean_object* v_size_1328_; 
v_size_1328_ = lean_ctor_get(v_r_1301_, 0);
lean_inc(v_size_1328_);
v___y_1312_ = v___x_1327_;
v___y_1313_ = v___x_1326_;
v___y_1314_ = v_size_1328_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___y_1312_ = v___x_1327_;
v___y_1313_ = v___x_1326_;
v___y_1314_ = v___x_1329_;
goto v___jp_1311_;
}
}
}
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1339_ = lean_nat_add(v___x_1276_, v_size_1285_);
v___x_1340_ = lean_nat_add(v___x_1339_, v_size_1271_);
lean_dec(v_size_1271_);
v___x_1341_ = lean_nat_add(v___x_1339_, v_size_1297_);
lean_dec(v___x_1339_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 4, v_l_1274_);
lean_ctor_set(v___x_1295_, 3, v_tree_1282_);
lean_ctor_set(v___x_1295_, 2, v_v_1284_);
lean_ctor_set(v___x_1295_, 1, v_k_1283_);
lean_ctor_set(v___x_1295_, 0, v___x_1341_);
v___x_1343_ = v___x_1295_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1283_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1284_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_tree_1282_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_l_1274_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1345_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_r_1275_);
lean_ctor_set(v___x_1279_, 3, v___x_1343_);
lean_ctor_set(v___x_1279_, 2, v_v_1273_);
lean_ctor_set(v___x_1279_, 1, v_k_1272_);
lean_ctor_set(v___x_1279_, 0, v___x_1340_);
v___x_1345_ = v___x_1279_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1275_);
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
}
}
else
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1407_; 
lean_inc(v_r_1275_);
lean_inc(v_v_1273_);
lean_inc(v_k_1272_);
lean_inc(v_size_1271_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1408_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_r_1087_, 2);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_r_1087_, 1);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1412_);
v___x_1355_ = v_r_1087_;
v_isShared_1356_ = v_isSharedCheck_1407_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_r_1087_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1407_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
if (lean_obj_tag(v_l_1274_) == 0)
{
if (lean_obj_tag(v_r_1275_) == 0)
{
lean_object* v_k_1357_; lean_object* v_v_1358_; lean_object* v_size_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_inc(v_tree_1282_);
v_k_1357_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_k_1357_);
v_v_1358_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_v_1358_);
lean_dec_ref(v___x_1281_);
v_size_1359_ = lean_ctor_get(v_l_1274_, 0);
v___x_1360_ = lean_nat_add(v___x_1276_, v_size_1271_);
lean_dec(v_size_1271_);
v___x_1361_ = lean_nat_add(v___x_1276_, v_size_1359_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_l_1274_);
lean_ctor_set(v___x_1355_, 3, v_tree_1282_);
lean_ctor_set(v___x_1355_, 2, v_v_1358_);
lean_ctor_set(v___x_1355_, 1, v_k_1357_);
lean_ctor_set(v___x_1355_, 0, v___x_1361_);
v___x_1363_ = v___x_1355_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_tree_1282_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_l_1274_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_r_1275_);
lean_ctor_set(v___x_1279_, 3, v___x_1363_);
lean_ctor_set(v___x_1279_, 2, v_v_1273_);
lean_ctor_set(v___x_1279_, 1, v_k_1272_);
lean_ctor_set(v___x_1279_, 0, v___x_1360_);
v___x_1365_ = v___x_1279_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1275_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_k_1368_; lean_object* v_v_1369_; lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_size_1271_);
v_k_1368_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_k_1368_);
v_v_1369_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_v_1369_);
lean_dec_ref(v___x_1281_);
v_k_1370_ = lean_ctor_get(v_l_1274_, 1);
v_v_1371_ = lean_ctor_get(v_l_1274_, 2);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_l_1274_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; 
v_unused_1386_ = lean_ctor_get(v_l_1274_, 4);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_l_1274_, 3);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_l_1274_, 0);
lean_dec(v_unused_1388_);
v___x_1373_ = v_l_1274_;
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_v_1371_);
lean_inc(v_k_1370_);
lean_dec(v_l_1274_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(3u);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 4, v_r_1275_);
lean_ctor_set(v___x_1373_, 3, v_r_1275_);
lean_ctor_set(v___x_1373_, 2, v_v_1369_);
lean_ctor_set(v___x_1373_, 1, v_k_1368_);
lean_ctor_set(v___x_1373_, 0, v___x_1276_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1275_);
v___x_1377_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 3, v_r_1275_);
lean_ctor_set(v___x_1355_, 0, v___x_1276_);
v___x_1379_ = v___x_1355_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_r_1275_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v___x_1379_);
lean_ctor_set(v___x_1279_, 3, v___x_1377_);
lean_ctor_set(v___x_1279_, 2, v_v_1371_);
lean_ctor_set(v___x_1279_, 1, v_k_1370_);
lean_ctor_set(v___x_1279_, 0, v___x_1375_);
v___x_1381_ = v___x_1279_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1275_) == 0)
{
lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec(v_size_1271_);
v_k_1389_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_k_1389_);
v_v_1390_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_v_1390_);
lean_dec_ref(v___x_1281_);
v___x_1391_ = lean_unsigned_to_nat(3u);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_l_1274_);
lean_ctor_set(v___x_1355_, 2, v_v_1390_);
lean_ctor_set(v___x_1355_, 1, v_k_1389_);
lean_ctor_set(v___x_1355_, 0, v___x_1276_);
v___x_1393_ = v___x_1355_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_l_1274_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_l_1274_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v_r_1275_);
lean_ctor_set(v___x_1279_, 3, v___x_1393_);
lean_ctor_set(v___x_1279_, 2, v_v_1273_);
lean_ctor_set(v___x_1279_, 1, v_k_1272_);
lean_ctor_set(v___x_1279_, 0, v___x_1391_);
v___x_1395_ = v___x_1279_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1275_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_k_1398_; lean_object* v_v_1399_; lean_object* v___x_1401_; 
v_k_1398_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_k_1398_);
v_v_1399_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_v_1399_);
lean_dec_ref(v___x_1281_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 3, v_r_1275_);
v___x_1401_ = v___x_1355_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_size_1271_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_r_1275_);
v___x_1401_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_unsigned_to_nat(2u);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 4, v___x_1401_);
lean_ctor_set(v___x_1279_, 3, v_r_1275_);
lean_ctor_set(v___x_1279_, 2, v_v_1399_);
lean_ctor_set(v___x_1279_, 1, v_k_1398_);
lean_ctor_set(v___x_1279_, 0, v___x_1402_);
v___x_1404_ = v___x_1279_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_k_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_v_1399_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_r_1275_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v___x_1401_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
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
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1571_; 
lean_inc(v_r_1275_);
lean_inc(v_v_1273_);
lean_inc(v_k_1272_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1572_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_r_1087_, 2);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_r_1087_, 1);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1576_);
v___x_1420_ = v_r_1087_;
v_isShared_1421_ = v_isSharedCheck_1571_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v_r_1087_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1571_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v_tree_1423_; 
v___x_1422_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1272_, v_v_1273_, v_l_1274_, v_r_1275_);
v_tree_1423_ = lean_ctor_get(v___x_1422_, 2);
lean_inc(v_tree_1423_);
if (lean_obj_tag(v_tree_1423_) == 0)
{
lean_object* v_k_1424_; lean_object* v_v_1425_; lean_object* v_size_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_k_1424_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_k_1424_);
v_v_1425_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_v_1425_);
lean_dec_ref(v___x_1422_);
v_size_1426_ = lean_ctor_get(v_tree_1423_, 0);
v___x_1427_ = lean_unsigned_to_nat(3u);
v___x_1428_ = lean_nat_mul(v___x_1427_, v_size_1426_);
v___x_1429_ = lean_nat_dec_lt(v___x_1428_, v_size_1266_);
lean_dec(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec(v_r_1270_);
v___x_1430_ = lean_nat_add(v___x_1276_, v_size_1266_);
v___x_1431_ = lean_nat_add(v___x_1430_, v_size_1426_);
lean_dec(v___x_1430_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_tree_1423_);
lean_ctor_set(v___x_1420_, 3, v_l_1086_);
lean_ctor_set(v___x_1420_, 2, v_v_1425_);
lean_ctor_set(v___x_1420_, 1, v_k_1424_);
lean_ctor_set(v___x_1420_, 0, v___x_1431_);
v___x_1433_ = v___x_1420_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_tree_1423_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1500_; 
lean_inc(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
lean_inc(v_size_1266_);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1501_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1505_);
v___x_1436_ = v_l_1086_;
v_isShared_1437_ = v_isSharedCheck_1500_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v_l_1086_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1500_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_size_1438_; lean_object* v_size_1439_; lean_object* v_k_1440_; lean_object* v_v_1441_; lean_object* v_l_1442_; lean_object* v_r_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_size_1438_ = lean_ctor_get(v_l_1269_, 0);
v_size_1439_ = lean_ctor_get(v_r_1270_, 0);
v_k_1440_ = lean_ctor_get(v_r_1270_, 1);
v_v_1441_ = lean_ctor_get(v_r_1270_, 2);
v_l_1442_ = lean_ctor_get(v_r_1270_, 3);
v_r_1443_ = lean_ctor_get(v_r_1270_, 4);
v___x_1444_ = lean_unsigned_to_nat(2u);
v___x_1445_ = lean_nat_mul(v___x_1444_, v_size_1438_);
v___x_1446_ = lean_nat_dec_lt(v_size_1439_, v___x_1445_);
lean_dec(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1484_; 
lean_inc(v_r_1443_);
lean_inc(v_l_1442_);
lean_inc(v_v_1441_);
lean_inc(v_k_1440_);
lean_del_object(v___x_1436_);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_r_1270_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1485_ = lean_ctor_get(v_r_1270_, 4);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_r_1270_, 3);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_r_1270_, 2);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1270_, 1);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_r_1270_, 0);
lean_dec(v_unused_1489_);
v___x_1448_ = v_r_1270_;
v_isShared_1449_ = v_isSharedCheck_1484_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_r_1270_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1484_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___x_1472_; lean_object* v___y_1474_; 
v___x_1450_ = lean_nat_add(v___x_1276_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1451_ = lean_nat_add(v___x_1450_, v_size_1426_);
lean_dec(v___x_1450_);
v___x_1472_ = lean_nat_add(v___x_1276_, v_size_1438_);
if (lean_obj_tag(v_l_1442_) == 0)
{
lean_object* v_size_1482_; 
v_size_1482_ = lean_ctor_get(v_l_1442_, 0);
lean_inc(v_size_1482_);
v___y_1474_ = v_size_1482_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___y_1474_ = v___x_1483_;
goto v___jp_1473_;
}
v___jp_1452_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_nat_add(v___y_1453_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec(v___y_1453_);
lean_inc_ref(v_tree_1423_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 4, v_tree_1423_);
lean_ctor_set(v___x_1448_, 3, v_r_1443_);
lean_ctor_set(v___x_1448_, 2, v_v_1425_);
lean_ctor_set(v___x_1448_, 1, v_k_1424_);
lean_ctor_set(v___x_1448_, 0, v___x_1456_);
v___x_1458_ = v___x_1448_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_k_1424_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_v_1425_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_r_1443_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v_tree_1423_);
v___x_1458_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_isSharedCheck_1465_ = !lean_is_exclusive(v_tree_1423_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1466_ = lean_ctor_get(v_tree_1423_, 4);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_tree_1423_, 3);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_tree_1423_, 2);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_tree_1423_, 1);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_tree_1423_, 0);
lean_dec(v_unused_1470_);
v___x_1460_ = v_tree_1423_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_tree_1423_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 4, v___x_1458_);
lean_ctor_set(v___x_1460_, 3, v___y_1454_);
lean_ctor_set(v___x_1460_, 2, v_v_1441_);
lean_ctor_set(v___x_1460_, 1, v_k_1440_);
lean_ctor_set(v___x_1460_, 0, v___x_1451_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v___y_1454_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v___x_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_nat_add(v___x_1472_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec(v___x_1472_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_l_1442_);
lean_ctor_set(v___x_1420_, 3, v_l_1269_);
lean_ctor_set(v___x_1420_, 2, v_v_1268_);
lean_ctor_set(v___x_1420_, 1, v_k_1267_);
lean_ctor_set(v___x_1420_, 0, v___x_1475_);
v___x_1477_ = v___x_1420_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_l_1442_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_nat_add(v___x_1276_, v_size_1426_);
if (lean_obj_tag(v_r_1443_) == 0)
{
lean_object* v_size_1479_; 
v_size_1479_ = lean_ctor_get(v_r_1443_, 0);
lean_inc(v_size_1479_);
v___y_1453_ = v___x_1478_;
v___y_1454_ = v___x_1477_;
v___y_1455_ = v_size_1479_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___y_1453_ = v___x_1478_;
v___y_1454_ = v___x_1477_;
v___y_1455_ = v___x_1480_;
goto v___jp_1452_;
}
}
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1490_ = lean_nat_add(v___x_1276_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1491_ = lean_nat_add(v___x_1490_, v_size_1426_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_nat_add(v___x_1276_, v_size_1426_);
v___x_1493_ = lean_nat_add(v___x_1492_, v_size_1439_);
lean_dec(v___x_1492_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_tree_1423_);
lean_ctor_set(v___x_1420_, 3, v_r_1270_);
lean_ctor_set(v___x_1420_, 2, v_v_1425_);
lean_ctor_set(v___x_1420_, 1, v_k_1424_);
lean_ctor_set(v___x_1420_, 0, v___x_1493_);
v___x_1495_ = v___x_1420_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1424_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1425_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_tree_1423_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 4, v___x_1495_);
lean_ctor_set(v___x_1436_, 0, v___x_1491_);
v___x_1497_ = v___x_1436_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1269_) == 0)
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1529_; 
lean_inc_ref(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
lean_inc(v_size_1266_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1530_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1534_);
v___x_1507_ = v_l_1086_;
v_isShared_1508_ = v_isSharedCheck_1529_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_l_1086_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1529_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
if (lean_obj_tag(v_r_1270_) == 0)
{
lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v_size_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v_k_1509_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_k_1509_);
v_v_1510_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_v_1510_);
lean_dec_ref(v___x_1422_);
v_size_1511_ = lean_ctor_get(v_r_1270_, 0);
v___x_1512_ = lean_nat_add(v___x_1276_, v_size_1266_);
lean_dec(v_size_1266_);
v___x_1513_ = lean_nat_add(v___x_1276_, v_size_1511_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_tree_1423_);
lean_ctor_set(v___x_1420_, 3, v_r_1270_);
lean_ctor_set(v___x_1420_, 2, v_v_1510_);
lean_ctor_set(v___x_1420_, 1, v_k_1509_);
lean_ctor_set(v___x_1420_, 0, v___x_1513_);
v___x_1515_ = v___x_1420_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_tree_1423_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v___x_1515_);
lean_ctor_set(v___x_1507_, 0, v___x_1512_);
v___x_1517_ = v___x_1507_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec(v_size_1266_);
v_k_1520_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_v_1521_);
lean_dec_ref(v___x_1422_);
v___x_1522_ = lean_unsigned_to_nat(3u);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_r_1270_);
lean_ctor_set(v___x_1420_, 3, v_r_1270_);
lean_ctor_set(v___x_1420_, 2, v_v_1521_);
lean_ctor_set(v___x_1420_, 1, v_k_1520_);
lean_ctor_set(v___x_1420_, 0, v___x_1276_);
v___x_1524_ = v___x_1420_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1270_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v___x_1524_);
lean_ctor_set(v___x_1507_, 0, v___x_1522_);
v___x_1526_ = v___x_1507_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1270_) == 0)
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1559_; 
lean_inc(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; 
v_unused_1560_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1564_);
v___x_1536_ = v_l_1086_;
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_l_1086_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1555_; 
v_k_1538_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_k_1538_);
v_v_1539_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_v_1539_);
lean_dec_ref(v___x_1422_);
v_k_1540_ = lean_ctor_get(v_r_1270_, 1);
v_v_1541_ = lean_ctor_get(v_r_1270_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_r_1270_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1556_ = lean_ctor_get(v_r_1270_, 4);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_r_1270_, 3);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_r_1270_, 0);
lean_dec(v_unused_1558_);
v___x_1543_ = v_r_1270_;
v_isShared_1544_ = v_isSharedCheck_1555_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_v_1541_);
lean_inc(v_k_1540_);
lean_dec(v_r_1270_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1555_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(3u);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_l_1269_);
lean_ctor_set(v___x_1543_, 3, v_l_1269_);
lean_ctor_set(v___x_1543_, 2, v_v_1268_);
lean_ctor_set(v___x_1543_, 1, v_k_1267_);
lean_ctor_set(v___x_1543_, 0, v___x_1276_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_l_1269_);
v___x_1547_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_l_1269_);
lean_ctor_set(v___x_1420_, 3, v_l_1269_);
lean_ctor_set(v___x_1420_, 2, v_v_1539_);
lean_ctor_set(v___x_1420_, 1, v_k_1538_);
lean_ctor_set(v___x_1420_, 0, v___x_1276_);
v___x_1549_ = v___x_1420_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_l_1269_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_l_1269_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 4, v___x_1549_);
lean_ctor_set(v___x_1536_, 3, v___x_1547_);
lean_ctor_set(v___x_1536_, 2, v_v_1541_);
lean_ctor_set(v___x_1536_, 1, v_k_1540_);
lean_ctor_set(v___x_1536_, 0, v___x_1545_);
v___x_1551_ = v___x_1536_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
else
{
lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v_k_1565_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_k_1565_);
v_v_1566_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_v_1566_);
lean_dec_ref(v___x_1422_);
v___x_1567_ = lean_unsigned_to_nat(2u);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_r_1270_);
lean_ctor_set(v___x_1420_, 3, v_l_1086_);
lean_ctor_set(v___x_1420_, 2, v_v_1566_);
lean_ctor_set(v___x_1420_, 1, v_k_1565_);
lean_ctor_set(v___x_1420_, 0, v___x_1567_);
v___x_1569_ = v___x_1420_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1565_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1566_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_r_1270_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
}
else
{
return v_l_1086_;
}
}
else
{
return v_r_1087_;
}
}
default: 
{
lean_object* v_impl_1577_; lean_object* v___x_1578_; 
v_impl_1577_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1082_, v_r_1087_);
v___x_1578_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1577_) == 0)
{
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_size_1579_; lean_object* v_size_1580_; lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_l_1583_; lean_object* v_r_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_size_1579_ = lean_ctor_get(v_impl_1577_, 0);
v_size_1580_ = lean_ctor_get(v_l_1086_, 0);
v_k_1581_ = lean_ctor_get(v_l_1086_, 1);
v_v_1582_ = lean_ctor_get(v_l_1086_, 2);
v_l_1583_ = lean_ctor_get(v_l_1086_, 3);
v_r_1584_ = lean_ctor_get(v_l_1086_, 4);
lean_inc(v_r_1584_);
v___x_1585_ = lean_unsigned_to_nat(3u);
v___x_1586_ = lean_nat_mul(v___x_1585_, v_size_1579_);
v___x_1587_ = lean_nat_dec_lt(v___x_1586_, v_size_1580_);
lean_dec(v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec(v_r_1584_);
v___x_1588_ = lean_nat_add(v___x_1578_, v_size_1580_);
v___x_1589_ = lean_nat_add(v___x_1588_, v_size_1579_);
lean_dec(v___x_1588_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_impl_1577_);
lean_ctor_set(v___x_1089_, 0, v___x_1589_);
v___x_1591_ = v___x_1089_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_impl_1577_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
else
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1658_; 
lean_inc(v_l_1583_);
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
lean_inc(v_size_1580_);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1659_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1663_);
v___x_1594_ = v_l_1086_;
v_isShared_1595_ = v_isSharedCheck_1658_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_l_1086_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1658_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_size_1596_; lean_object* v_size_1597_; lean_object* v_k_1598_; lean_object* v_v_1599_; lean_object* v_l_1600_; lean_object* v_r_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_size_1596_ = lean_ctor_get(v_l_1583_, 0);
v_size_1597_ = lean_ctor_get(v_r_1584_, 0);
v_k_1598_ = lean_ctor_get(v_r_1584_, 1);
v_v_1599_ = lean_ctor_get(v_r_1584_, 2);
v_l_1600_ = lean_ctor_get(v_r_1584_, 3);
v_r_1601_ = lean_ctor_get(v_r_1584_, 4);
v___x_1602_ = lean_unsigned_to_nat(2u);
v___x_1603_ = lean_nat_mul(v___x_1602_, v_size_1596_);
v___x_1604_ = lean_nat_dec_lt(v_size_1597_, v___x_1603_);
lean_dec(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1633_; 
lean_inc(v_r_1601_);
lean_inc(v_l_1600_);
lean_inc(v_v_1599_);
lean_inc(v_k_1598_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_r_1584_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1634_ = lean_ctor_get(v_r_1584_, 4);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_r_1584_, 3);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_r_1584_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_r_1584_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1584_, 0);
lean_dec(v_unused_1638_);
v___x_1606_ = v_r_1584_;
v_isShared_1607_ = v_isSharedCheck_1633_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_r_1584_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1633_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___x_1621_; lean_object* v___y_1623_; 
v___x_1608_ = lean_nat_add(v___x_1578_, v_size_1580_);
lean_dec(v_size_1580_);
v___x_1609_ = lean_nat_add(v___x_1608_, v_size_1579_);
lean_dec(v___x_1608_);
v___x_1621_ = lean_nat_add(v___x_1578_, v_size_1596_);
if (lean_obj_tag(v_l_1600_) == 0)
{
lean_object* v_size_1631_; 
v_size_1631_ = lean_ctor_get(v_l_1600_, 0);
lean_inc(v_size_1631_);
v___y_1623_ = v_size_1631_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___y_1623_ = v___x_1632_;
goto v___jp_1622_;
}
v___jp_1610_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_nat_add(v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec(v___y_1612_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 4, v_impl_1577_);
lean_ctor_set(v___x_1606_, 3, v_r_1601_);
lean_ctor_set(v___x_1606_, 2, v_v_1085_);
lean_ctor_set(v___x_1606_, 1, v_k_1084_);
lean_ctor_set(v___x_1606_, 0, v___x_1614_);
v___x_1616_ = v___x_1606_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_r_1601_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_impl_1577_);
v___x_1616_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v___x_1616_);
lean_ctor_set(v___x_1594_, 3, v___y_1611_);
lean_ctor_set(v___x_1594_, 2, v_v_1599_);
lean_ctor_set(v___x_1594_, 1, v_k_1598_);
lean_ctor_set(v___x_1594_, 0, v___x_1609_);
v___x_1618_ = v___x_1594_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1598_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v___y_1611_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_nat_add(v___x_1621_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec(v___x_1621_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1600_);
lean_ctor_set(v___x_1089_, 3, v_l_1583_);
lean_ctor_set(v___x_1089_, 2, v_v_1582_);
lean_ctor_set(v___x_1089_, 1, v_k_1581_);
lean_ctor_set(v___x_1089_, 0, v___x_1624_);
v___x_1626_ = v___x_1089_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_l_1583_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_l_1600_);
v___x_1626_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_nat_add(v___x_1578_, v_size_1579_);
if (lean_obj_tag(v_r_1601_) == 0)
{
lean_object* v_size_1628_; 
v_size_1628_ = lean_ctor_get(v_r_1601_, 0);
lean_inc(v_size_1628_);
v___y_1611_ = v___x_1626_;
v___y_1612_ = v___x_1627_;
v___y_1613_ = v_size_1628_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___y_1611_ = v___x_1626_;
v___y_1612_ = v___x_1627_;
v___y_1613_ = v___x_1629_;
goto v___jp_1610_;
}
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_del_object(v___x_1089_);
v___x_1639_ = lean_nat_add(v___x_1578_, v_size_1580_);
lean_dec(v_size_1580_);
v___x_1640_ = lean_nat_add(v___x_1639_, v_size_1579_);
lean_dec(v___x_1639_);
v___x_1641_ = lean_nat_add(v___x_1578_, v_size_1579_);
v___x_1642_ = lean_nat_add(v___x_1641_, v_size_1597_);
lean_dec(v___x_1641_);
lean_inc_ref(v_impl_1577_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v_impl_1577_);
lean_ctor_set(v___x_1594_, 3, v_r_1584_);
lean_ctor_set(v___x_1594_, 2, v_v_1085_);
lean_ctor_set(v___x_1594_, 1, v_k_1084_);
lean_ctor_set(v___x_1594_, 0, v___x_1642_);
v___x_1644_ = v___x_1594_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_r_1584_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_impl_1577_);
v___x_1644_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_isSharedCheck_1651_ = !lean_is_exclusive(v_impl_1577_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1652_ = lean_ctor_get(v_impl_1577_, 4);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_impl_1577_, 3);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_impl_1577_, 2);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_impl_1577_, 1);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_impl_1577_, 0);
lean_dec(v_unused_1656_);
v___x_1646_ = v_impl_1577_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v_impl_1577_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 4, v___x_1644_);
lean_ctor_set(v___x_1646_, 3, v_l_1583_);
lean_ctor_set(v___x_1646_, 2, v_v_1582_);
lean_ctor_set(v___x_1646_, 1, v_k_1581_);
lean_ctor_set(v___x_1646_, 0, v___x_1640_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_l_1583_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v___x_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v_size_1664_ = lean_ctor_get(v_impl_1577_, 0);
v___x_1665_ = lean_nat_add(v___x_1578_, v_size_1664_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_impl_1577_);
lean_ctor_set(v___x_1089_, 0, v___x_1665_);
v___x_1667_ = v___x_1089_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_impl_1577_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_l_1669_; 
v_l_1669_ = lean_ctor_get(v_l_1086_, 3);
if (lean_obj_tag(v_l_1669_) == 0)
{
lean_object* v_r_1670_; 
lean_inc_ref(v_l_1669_);
v_r_1670_ = lean_ctor_get(v_l_1086_, 4);
lean_inc(v_r_1670_);
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_size_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1686_; 
v_size_1671_ = lean_ctor_get(v_l_1086_, 0);
v_k_1672_ = lean_ctor_get(v_l_1086_, 1);
v_v_1673_ = lean_ctor_get(v_l_1086_, 2);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1687_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1688_);
v___x_1675_ = v_l_1086_;
v_isShared_1676_ = v_isSharedCheck_1686_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_inc(v_size_1671_);
lean_dec(v_l_1086_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1686_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_size_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v_size_1677_ = lean_ctor_get(v_r_1670_, 0);
v___x_1678_ = lean_nat_add(v___x_1578_, v_size_1671_);
lean_dec(v_size_1671_);
v___x_1679_ = lean_nat_add(v___x_1578_, v_size_1677_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v_impl_1577_);
lean_ctor_set(v___x_1675_, 3, v_r_1670_);
lean_ctor_set(v___x_1675_, 2, v_v_1085_);
lean_ctor_set(v___x_1675_, 1, v_k_1084_);
lean_ctor_set(v___x_1675_, 0, v___x_1679_);
v___x_1681_ = v___x_1675_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_impl_1577_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1681_);
lean_ctor_set(v___x_1089_, 3, v_l_1669_);
lean_ctor_set(v___x_1089_, 2, v_v_1673_);
lean_ctor_set(v___x_1089_, 1, v_k_1672_);
lean_ctor_set(v___x_1089_, 0, v___x_1678_);
v___x_1683_ = v___x_1089_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1669_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_k_1689_; lean_object* v_v_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1701_; 
v_k_1689_ = lean_ctor_get(v_l_1086_, 1);
v_v_1690_ = lean_ctor_get(v_l_1086_, 2);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; 
v_unused_1702_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1704_);
v___x_1692_ = v_l_1086_;
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_v_1690_);
lean_inc(v_k_1689_);
lean_dec(v_l_1086_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_unsigned_to_nat(3u);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 3, v_r_1670_);
lean_ctor_set(v___x_1692_, 2, v_v_1085_);
lean_ctor_set(v___x_1692_, 1, v_k_1084_);
lean_ctor_set(v___x_1692_, 0, v___x_1578_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_r_1670_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1696_);
lean_ctor_set(v___x_1089_, 3, v_l_1669_);
lean_ctor_set(v___x_1089_, 2, v_v_1690_);
lean_ctor_set(v___x_1089_, 1, v_k_1689_);
lean_ctor_set(v___x_1089_, 0, v___x_1694_);
v___x_1698_ = v___x_1089_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1689_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_l_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
else
{
lean_object* v_r_1705_; 
v_r_1705_ = lean_ctor_get(v_l_1086_, 4);
lean_inc(v_r_1705_);
if (lean_obj_tag(v_r_1705_) == 0)
{
lean_object* v_k_1706_; lean_object* v_v_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1730_; 
lean_inc(v_l_1669_);
v_k_1706_ = lean_ctor_get(v_l_1086_, 1);
v_v_1707_ = lean_ctor_get(v_l_1086_, 2);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; 
v_unused_1731_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1733_);
v___x_1709_ = v_l_1086_;
v_isShared_1710_ = v_isSharedCheck_1730_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_v_1707_);
lean_inc(v_k_1706_);
lean_dec(v_l_1086_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1730_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1726_; 
v_k_1711_ = lean_ctor_get(v_r_1705_, 1);
v_v_1712_ = lean_ctor_get(v_r_1705_, 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_r_1705_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; lean_object* v_unused_1728_; lean_object* v_unused_1729_; 
v_unused_1727_ = lean_ctor_get(v_r_1705_, 4);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v_r_1705_, 3);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_r_1705_, 0);
lean_dec(v_unused_1729_);
v___x_1714_ = v_r_1705_;
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_v_1712_);
lean_inc(v_k_1711_);
lean_dec(v_r_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_unsigned_to_nat(3u);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_l_1669_);
lean_ctor_set(v___x_1714_, 3, v_l_1669_);
lean_ctor_set(v___x_1714_, 2, v_v_1707_);
lean_ctor_set(v___x_1714_, 1, v_k_1706_);
lean_ctor_set(v___x_1714_, 0, v___x_1578_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1706_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1707_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_l_1669_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_l_1669_);
v___x_1718_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 4, v_l_1669_);
lean_ctor_set(v___x_1709_, 2, v_v_1085_);
lean_ctor_set(v___x_1709_, 1, v_k_1084_);
lean_ctor_set(v___x_1709_, 0, v___x_1578_);
v___x_1720_ = v___x_1709_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_l_1669_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_l_1669_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1720_);
lean_ctor_set(v___x_1089_, 3, v___x_1718_);
lean_ctor_set(v___x_1089_, 2, v_v_1712_);
lean_ctor_set(v___x_1089_, 1, v_k_1711_);
lean_ctor_set(v___x_1089_, 0, v___x_1716_);
v___x_1722_ = v___x_1089_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v___x_1720_);
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
else
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(2u);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_r_1705_);
lean_ctor_set(v___x_1089_, 0, v___x_1734_);
v___x_1736_ = v___x_1089_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_r_1705_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v___x_1739_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1086_);
lean_ctor_set(v___x_1089_, 0, v___x_1578_);
v___x_1739_ = v___x_1089_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_l_1086_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
}
else
{
return v_t_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1743_, lean_object* v_t_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1743_, v_t_1744_);
lean_dec(v_k_1743_);
return v_res_1745_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1746_, lean_object* v_declName_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_ext_1753_; lean_object* v_toEnvExtension_1754_; lean_object* v_env_1755_; lean_object* v_asyncMode_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___y_1760_; lean_object* v_funCC_1787_; uint8_t v___x_1788_; 
v___x_1751_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1752_ = lean_st_ref_get(v_a_1749_);
v_ext_1753_ = lean_ctor_get(v_ext_1746_, 1);
v_toEnvExtension_1754_ = lean_ctor_get(v_ext_1753_, 0);
v_env_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1752_);
v_asyncMode_1756_ = lean_ctor_get(v_toEnvExtension_1754_, 2);
v___x_1757_ = 0;
v___x_1758_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1751_, v_ext_1746_, v_env_1755_, v_asyncMode_1756_, v___x_1757_);
v_funCC_1787_ = lean_ctor_get(v___x_1758_, 2);
v___x_1788_ = l_Lean_NameSet_contains(v_funCC_1787_, v_declName_1747_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
lean_inc(v_declName_1747_);
v___x_1789_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
v___y_1760_ = v_a_1749_;
goto v___jp_1759_;
}
else
{
lean_dec(v___x_1758_);
lean_dec(v_declName_1747_);
lean_dec_ref(v_ext_1746_);
return v___x_1789_;
}
}
else
{
v___y_1760_ = v_a_1749_;
goto v___jp_1759_;
}
v___jp_1759_:
{
lean_object* v_funCC_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v_env_1765_; lean_object* v_nextMacroScope_1766_; lean_object* v_ngen_1767_; lean_object* v_auxDeclNGen_1768_; lean_object* v_traceState_1769_; lean_object* v_recordedDeps_1770_; lean_object* v_messages_1771_; lean_object* v_infoState_1772_; lean_object* v_snapshotTasks_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1785_; 
v_funCC_1761_ = lean_ctor_get(v___x_1758_, 2);
lean_inc(v_funCC_1761_);
lean_dec(v___x_1758_);
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1747_, v_funCC_1761_);
lean_dec(v_declName_1747_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1763_, 0, v___x_1762_);
v___x_1764_ = lean_st_ref_take(v___y_1760_);
v_env_1765_ = lean_ctor_get(v___x_1764_, 0);
v_nextMacroScope_1766_ = lean_ctor_get(v___x_1764_, 1);
v_ngen_1767_ = lean_ctor_get(v___x_1764_, 2);
v_auxDeclNGen_1768_ = lean_ctor_get(v___x_1764_, 3);
v_traceState_1769_ = lean_ctor_get(v___x_1764_, 4);
v_recordedDeps_1770_ = lean_ctor_get(v___x_1764_, 6);
v_messages_1771_ = lean_ctor_get(v___x_1764_, 7);
v_infoState_1772_ = lean_ctor_get(v___x_1764_, 8);
v_snapshotTasks_1773_ = lean_ctor_get(v___x_1764_, 9);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1764_, 5);
lean_dec(v_unused_1786_);
v___x_1775_ = v___x_1764_;
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snapshotTasks_1773_);
lean_inc(v_infoState_1772_);
lean_inc(v_messages_1771_);
lean_inc(v_recordedDeps_1770_);
lean_inc(v_traceState_1769_);
lean_inc(v_auxDeclNGen_1768_);
lean_inc(v_ngen_1767_);
lean_inc(v_nextMacroScope_1766_);
lean_inc(v_env_1765_);
lean_dec(v___x_1764_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1746_, v_env_1765_, v___f_1763_);
v___x_1779_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 5, v___x_1779_);
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1781_ = v___x_1775_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_nextMacroScope_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_ngen_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_auxDeclNGen_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_traceState_1769_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_recordedDeps_1770_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_messages_1771_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_infoState_1772_);
lean_ctor_set(v_reuseFailAlloc_1784_, 9, v_snapshotTasks_1773_);
v___x_1781_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_st_ref_put(v___y_1760_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1777_);
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1746_ = stack[0].m_obj;
lean_object* v_declName_1747_ = stack[1].m_obj;
lean_object* v_a_1748_ = stack[2].m_obj;
lean_object* v_a_1749_ = stack[3].m_obj;
lean_object* v_res_1790_;
v_res_1790_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1746_, v_declName_1747_, v_a_1748_, v_a_1749_);
stack->m_obj
 = v_res_1790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1791_, lean_object* v_declName_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1791_, v_declName_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1797_, lean_object* v_k_1798_, lean_object* v_t_1799_, lean_object* v_h_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1798_, v_t_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1802_, lean_object* v_k_1803_, lean_object* v_t_1804_, lean_object* v_h_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1802_, v_k_1803_, v_t_1804_, v_h_1805_);
lean_dec(v_k_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1807_, lean_object* v_s_1808_){
_start:
{
lean_object* v_casesTypes_1809_; lean_object* v_extThms_1810_; lean_object* v_funCC_1811_; lean_object* v_inj_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_casesTypes_1809_ = lean_ctor_get(v_s_1808_, 0);
v_extThms_1810_ = lean_ctor_get(v_s_1808_, 1);
v_funCC_1811_ = lean_ctor_get(v_s_1808_, 2);
v_inj_1812_ = lean_ctor_get(v_s_1808_, 4);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_s_1808_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v_s_1808_, 3);
lean_dec(v_unused_1820_);
v___x_1814_ = v_s_1808_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_inj_1812_);
lean_inc(v_funCC_1811_);
lean_inc(v_extThms_1810_);
lean_inc(v_casesTypes_1809_);
lean_dec(v_s_1808_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 3, v_a_1807_);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_casesTypes_1809_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_extThms_1810_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_funCC_1811_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_a_1807_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_inj_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_1822_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
lean_ctor_set(v___x_1822_, 2, v___x_1821_);
lean_ctor_set(v___x_1822_, 3, v___x_1821_);
lean_ctor_set(v___x_1822_, 4, v___x_1821_);
lean_ctor_set(v___x_1822_, 5, v___x_1821_);
return v___x_1822_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1823_, lean_object* v_declName_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v_ext_1832_; lean_object* v_toEnvExtension_1833_; lean_object* v_env_1834_; lean_object* v_asyncMode_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v_ematch_1838_; lean_object* v___x_1839_; 
v___x_1830_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1831_ = lean_st_ref_get(v_a_1828_);
v_ext_1832_ = lean_ctor_get(v_ext_1823_, 1);
v_toEnvExtension_1833_ = lean_ctor_get(v_ext_1832_, 0);
v_env_1834_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_ref(v_env_1834_);
lean_dec(v___x_1831_);
v_asyncMode_1835_ = lean_ctor_get(v_toEnvExtension_1833_, 2);
v___x_1836_ = 0;
v___x_1837_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1830_, v_ext_1823_, v_env_1834_, v_asyncMode_1835_, v___x_1836_);
v_ematch_1838_ = lean_ctor_get(v___x_1837_, 3);
lean_inc_ref(v_ematch_1838_);
lean_dec(v___x_1837_);
v___x_1839_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1838_, v_declName_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1885_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1885_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1885_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___f_1844_; lean_object* v___x_1845_; lean_object* v_env_1846_; lean_object* v_nextMacroScope_1847_; lean_object* v_ngen_1848_; lean_object* v_auxDeclNGen_1849_; lean_object* v_traceState_1850_; lean_object* v_recordedDeps_1851_; lean_object* v_messages_1852_; lean_object* v_infoState_1853_; lean_object* v_snapshotTasks_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1883_; 
v___f_1844_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1844_, 0, v_a_1840_);
v___x_1845_ = lean_st_ref_take(v_a_1828_);
v_env_1846_ = lean_ctor_get(v___x_1845_, 0);
v_nextMacroScope_1847_ = lean_ctor_get(v___x_1845_, 1);
v_ngen_1848_ = lean_ctor_get(v___x_1845_, 2);
v_auxDeclNGen_1849_ = lean_ctor_get(v___x_1845_, 3);
v_traceState_1850_ = lean_ctor_get(v___x_1845_, 4);
v_recordedDeps_1851_ = lean_ctor_get(v___x_1845_, 6);
v_messages_1852_ = lean_ctor_get(v___x_1845_, 7);
v_infoState_1853_ = lean_ctor_get(v___x_1845_, 8);
v_snapshotTasks_1854_ = lean_ctor_get(v___x_1845_, 9);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v___x_1845_, 5);
lean_dec(v_unused_1884_);
v___x_1856_ = v___x_1845_;
v_isShared_1857_ = v_isSharedCheck_1883_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_snapshotTasks_1854_);
lean_inc(v_infoState_1853_);
lean_inc(v_messages_1852_);
lean_inc(v_recordedDeps_1851_);
lean_inc(v_traceState_1850_);
lean_inc(v_auxDeclNGen_1849_);
lean_inc(v_ngen_1848_);
lean_inc(v_nextMacroScope_1847_);
lean_inc(v_env_1846_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1883_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1823_, v_env_1846_, v___f_1844_);
v___x_1859_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 5, v___x_1859_);
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_nextMacroScope_1847_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_ngen_1848_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_auxDeclNGen_1849_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v_traceState_1850_);
lean_ctor_set(v_reuseFailAlloc_1882_, 5, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1882_, 6, v_recordedDeps_1851_);
lean_ctor_set(v_reuseFailAlloc_1882_, 7, v_messages_1852_);
lean_ctor_set(v_reuseFailAlloc_1882_, 8, v_infoState_1853_);
lean_ctor_set(v_reuseFailAlloc_1882_, 9, v_snapshotTasks_1854_);
v___x_1861_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_mctx_1864_; lean_object* v_zetaDeltaFVarIds_1865_; lean_object* v_postponed_1866_; lean_object* v_diag_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1880_; 
v___x_1862_ = lean_st_ref_put(v_a_1828_, v___x_1861_);
v___x_1863_ = lean_st_ref_take(v_a_1826_);
v_mctx_1864_ = lean_ctor_get(v___x_1863_, 0);
v_zetaDeltaFVarIds_1865_ = lean_ctor_get(v___x_1863_, 2);
v_postponed_1866_ = lean_ctor_get(v___x_1863_, 3);
v_diag_1867_ = lean_ctor_get(v___x_1863_, 4);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1863_, 1);
lean_dec(v_unused_1881_);
v___x_1869_ = v___x_1863_;
v_isShared_1870_ = v_isSharedCheck_1880_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_diag_1867_);
lean_inc(v_postponed_1866_);
lean_inc(v_zetaDeltaFVarIds_1865_);
lean_inc(v_mctx_1864_);
lean_dec(v___x_1863_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1880_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_mctx_1864_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_zetaDeltaFVarIds_1865_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_postponed_1866_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_diag_1867_);
v___x_1874_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = lean_st_ref_put(v_a_1826_, v___x_1874_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1871_);
v___x_1877_ = v___x_1842_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1871_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v_ext_1823_);
v_a_1886_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1839_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1839_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1823_ = stack[0].m_obj;
lean_object* v_declName_1824_ = stack[1].m_obj;
lean_object* v_a_1825_ = stack[2].m_obj;
lean_object* v_a_1826_ = stack[3].m_obj;
lean_object* v_a_1827_ = stack[4].m_obj;
lean_object* v_a_1828_ = stack[5].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1823_, v_declName_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1895_, lean_object* v_declName_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1895_, v_declName_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1903_, lean_object* v_s_1904_){
_start:
{
lean_object* v_casesTypes_1905_; lean_object* v_extThms_1906_; lean_object* v_funCC_1907_; lean_object* v_ematch_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_casesTypes_1905_ = lean_ctor_get(v_s_1904_, 0);
v_extThms_1906_ = lean_ctor_get(v_s_1904_, 1);
v_funCC_1907_ = lean_ctor_get(v_s_1904_, 2);
v_ematch_1908_ = lean_ctor_get(v_s_1904_, 3);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_s_1904_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_s_1904_, 4);
lean_dec(v_unused_1916_);
v___x_1910_ = v_s_1904_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_ematch_1908_);
lean_inc(v_funCC_1907_);
lean_inc(v_extThms_1906_);
lean_inc(v_casesTypes_1905_);
lean_dec(v_s_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v_a_1903_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_casesTypes_1905_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_extThms_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_funCC_1907_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_ematch_1908_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_a_1903_);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1917_, lean_object* v_declName_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_ext_1926_; lean_object* v_toEnvExtension_1927_; lean_object* v_env_1928_; lean_object* v_asyncMode_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v_inj_1932_; lean_object* v___x_1933_; 
v___x_1924_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1925_ = lean_st_ref_get(v_a_1922_);
v_ext_1926_ = lean_ctor_get(v_ext_1917_, 1);
v_toEnvExtension_1927_ = lean_ctor_get(v_ext_1926_, 0);
v_env_1928_ = lean_ctor_get(v___x_1925_, 0);
lean_inc_ref(v_env_1928_);
lean_dec(v___x_1925_);
v_asyncMode_1929_ = lean_ctor_get(v_toEnvExtension_1927_, 2);
v___x_1930_ = 0;
v___x_1931_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1924_, v_ext_1917_, v_env_1928_, v_asyncMode_1929_, v___x_1930_);
v_inj_1932_ = lean_ctor_get(v___x_1931_, 4);
lean_inc_ref(v_inj_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1932_, v_declName_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1979_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1979_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1979_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v_env_1940_; lean_object* v_nextMacroScope_1941_; lean_object* v_ngen_1942_; lean_object* v_auxDeclNGen_1943_; lean_object* v_traceState_1944_; lean_object* v_recordedDeps_1945_; lean_object* v_messages_1946_; lean_object* v_infoState_1947_; lean_object* v_snapshotTasks_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1977_; 
v___f_1938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1938_, 0, v_a_1934_);
v___x_1939_ = lean_st_ref_take(v_a_1922_);
v_env_1940_ = lean_ctor_get(v___x_1939_, 0);
v_nextMacroScope_1941_ = lean_ctor_get(v___x_1939_, 1);
v_ngen_1942_ = lean_ctor_get(v___x_1939_, 2);
v_auxDeclNGen_1943_ = lean_ctor_get(v___x_1939_, 3);
v_traceState_1944_ = lean_ctor_get(v___x_1939_, 4);
v_recordedDeps_1945_ = lean_ctor_get(v___x_1939_, 6);
v_messages_1946_ = lean_ctor_get(v___x_1939_, 7);
v_infoState_1947_ = lean_ctor_get(v___x_1939_, 8);
v_snapshotTasks_1948_ = lean_ctor_get(v___x_1939_, 9);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v___x_1939_, 5);
lean_dec(v_unused_1978_);
v___x_1950_ = v___x_1939_;
v_isShared_1951_ = v_isSharedCheck_1977_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snapshotTasks_1948_);
lean_inc(v_infoState_1947_);
lean_inc(v_messages_1946_);
lean_inc(v_recordedDeps_1945_);
lean_inc(v_traceState_1944_);
lean_inc(v_auxDeclNGen_1943_);
lean_inc(v_ngen_1942_);
lean_inc(v_nextMacroScope_1941_);
lean_inc(v_env_1940_);
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1977_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1952_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1917_, v_env_1940_, v___f_1938_);
v___x_1953_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 5, v___x_1953_);
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_nextMacroScope_1941_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_ngen_1942_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_auxDeclNGen_1943_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v_traceState_1944_);
lean_ctor_set(v_reuseFailAlloc_1976_, 5, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1976_, 6, v_recordedDeps_1945_);
lean_ctor_set(v_reuseFailAlloc_1976_, 7, v_messages_1946_);
lean_ctor_set(v_reuseFailAlloc_1976_, 8, v_infoState_1947_);
lean_ctor_set(v_reuseFailAlloc_1976_, 9, v_snapshotTasks_1948_);
v___x_1955_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_mctx_1958_; lean_object* v_zetaDeltaFVarIds_1959_; lean_object* v_postponed_1960_; lean_object* v_diag_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1974_; 
v___x_1956_ = lean_st_ref_put(v_a_1922_, v___x_1955_);
v___x_1957_ = lean_st_ref_take(v_a_1920_);
v_mctx_1958_ = lean_ctor_get(v___x_1957_, 0);
v_zetaDeltaFVarIds_1959_ = lean_ctor_get(v___x_1957_, 2);
v_postponed_1960_ = lean_ctor_get(v___x_1957_, 3);
v_diag_1961_ = lean_ctor_get(v___x_1957_, 4);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1957_, 1);
lean_dec(v_unused_1975_);
v___x_1963_ = v___x_1957_;
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_diag_1961_);
lean_inc(v_postponed_1960_);
lean_inc(v_zetaDeltaFVarIds_1959_);
lean_inc(v_mctx_1958_);
lean_dec(v___x_1957_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_mctx_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_zetaDeltaFVarIds_1959_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_postponed_1960_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_diag_1961_);
v___x_1968_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_st_ref_put(v_a_1920_, v___x_1968_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1965_);
v___x_1971_ = v___x_1936_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1965_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_ext_1917_);
v_a_1980_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1933_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1933_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1917_ = stack[0].m_obj;
lean_object* v_declName_1918_ = stack[1].m_obj;
lean_object* v_a_1919_ = stack[2].m_obj;
lean_object* v_a_1920_ = stack[3].m_obj;
lean_object* v_a_1921_ = stack[4].m_obj;
lean_object* v_a_1922_ = stack[5].m_obj;
lean_object* v_res_1988_;
v_res_1988_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1917_, v_declName_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
stack->m_obj
 = v_res_1988_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1989_, lean_object* v_declName_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1989_, v_declName_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
return v_res_1996_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1997_, lean_object* v_i_1998_, lean_object* v_k_1999_){
_start:
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = lean_array_get_size(v_keys_1997_);
v___x_2001_ = lean_nat_dec_lt(v_i_1998_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_dec(v_i_1998_);
return v___x_2001_;
}
else
{
lean_object* v_k_x27_2002_; uint8_t v___x_2003_; 
v_k_x27_2002_ = lean_array_fget_borrowed(v_keys_1997_, v_i_1998_);
v___x_2003_ = lean_name_eq(v_k_1999_, v_k_x27_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_add(v_i_1998_, v___x_2004_);
lean_dec(v_i_1998_);
v_i_1998_ = v___x_2005_;
goto _start;
}
else
{
lean_dec(v_i_1998_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1997_ = stack[0].m_obj;
lean_object* v_i_1998_ = stack[1].m_obj;
lean_object* v_k_1999_ = stack[2].m_obj;
uint8_t v_res_2007_;
v_res_2007_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1997_, v_i_1998_, v_k_1999_);
stack->m_num = v_res_2007_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2008_, lean_object* v_i_2009_, lean_object* v_k_2010_){
_start:
{
uint8_t v_res_2011_; lean_object* v_r_2012_; 
v_res_2011_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2008_, v_i_2009_, v_k_2010_);
lean_dec(v_k_2010_);
lean_dec_ref(v_keys_2008_);
v_r_2012_ = lean_box(v_res_2011_);
return v_r_2012_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_2013_, size_t v_x_2014_, lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2013_) == 0)
{
lean_object* v_es_2016_; lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; lean_object* v_j_2020_; lean_object* v___x_2021_; 
v_es_2016_ = lean_ctor_get(v_x_2013_, 0);
v___x_2017_ = lean_box(2);
v___x_2018_ = ((size_t)31ULL);
v___x_2019_ = lean_usize_land(v_x_2014_, v___x_2018_);
v_j_2020_ = lean_usize_to_nat(v___x_2019_);
v___x_2021_ = lean_array_get_borrowed(v___x_2017_, v_es_2016_, v_j_2020_);
lean_dec(v_j_2020_);
switch(lean_obj_tag(v___x_2021_))
{
case 0:
{
lean_object* v_key_2022_; uint8_t v___x_2023_; 
v_key_2022_ = lean_ctor_get(v___x_2021_, 0);
v___x_2023_ = lean_name_eq(v_x_2015_, v_key_2022_);
return v___x_2023_;
}
case 1:
{
lean_object* v_node_2024_; size_t v___x_2025_; size_t v___x_2026_; 
v_node_2024_ = lean_ctor_get(v___x_2021_, 0);
v___x_2025_ = ((size_t)5ULL);
v___x_2026_ = lean_usize_shift_right(v_x_2014_, v___x_2025_);
v_x_2013_ = v_node_2024_;
v_x_2014_ = v___x_2026_;
goto _start;
}
default: 
{
uint8_t v___x_2028_; 
v___x_2028_ = 0;
return v___x_2028_;
}
}
}
else
{
lean_object* v_ks_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_ks_2029_ = lean_ctor_get(v_x_2013_, 0);
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_2029_, v___x_2030_, v_x_2015_);
return v___x_2031_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2013_ = stack[0].m_obj;
size_t v_x_2014_ = stack[1].m_num;
lean_object* v_x_2015_ = stack[2].m_obj;
uint8_t v_res_2032_;
v_res_2032_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2013_, v_x_2014_, v_x_2015_);
stack->m_num = v_res_2032_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
size_t v_x_336__boxed_2036_; uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_x_336__boxed_2036_ = lean_unbox_usize(v_x_2034_);
lean_dec(v_x_2034_);
v_res_2037_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2033_, v_x_336__boxed_2036_, v_x_2035_);
lean_dec(v_x_2035_);
lean_dec_ref(v_x_2033_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
uint64_t v___y_2042_; 
if (lean_obj_tag(v_x_2040_) == 0)
{
uint64_t v___x_2045_; 
v___x_2045_ = 1723ULL;
v___y_2042_ = v___x_2045_;
goto v___jp_2041_;
}
else
{
uint64_t v_hash_2046_; 
v_hash_2046_ = lean_ctor_get_uint64(v_x_2040_, sizeof(void*)*2);
v___y_2042_ = v_hash_2046_;
goto v___jp_2041_;
}
v___jp_2041_:
{
size_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_uint64_to_usize(v___y_2042_);
v___x_2044_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2039_, v___x_2043_, v_x_2040_);
return v___x_2044_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2039_ = stack[0].m_obj;
lean_object* v_x_2040_ = stack[1].m_obj;
uint8_t v_res_2047_;
v_res_2047_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2039_, v_x_2040_);
stack->m_num = v_res_2047_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2048_, v_x_2049_);
lean_dec(v_x_2049_);
lean_dec_ref(v_x_2048_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2052_, lean_object* v_declName_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_ext_2058_; lean_object* v_toEnvExtension_2059_; lean_object* v_env_2060_; lean_object* v_asyncMode_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v_extThms_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2056_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2057_ = lean_st_ref_get(v_a_2054_);
v_ext_2058_ = lean_ctor_get(v_ext_2052_, 1);
v_toEnvExtension_2059_ = lean_ctor_get(v_ext_2058_, 0);
v_env_2060_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_env_2060_);
lean_dec(v___x_2057_);
v_asyncMode_2061_ = lean_ctor_get(v_toEnvExtension_2059_, 2);
v___x_2062_ = 0;
v___x_2063_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2056_, v_ext_2052_, v_env_2060_, v_asyncMode_2061_, v___x_2062_);
v_extThms_2064_ = lean_ctor_get(v___x_2063_, 1);
lean_inc_ref(v_extThms_2064_);
lean_dec(v___x_2063_);
v___x_2065_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2064_, v_declName_2053_);
lean_dec_ref(v_extThms_2064_);
v___x_2066_ = lean_box(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2052_ = stack[0].m_obj;
lean_object* v_declName_2053_ = stack[1].m_obj;
lean_object* v_a_2054_ = stack[2].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2052_, v_declName_2053_, v_a_2054_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2069_, lean_object* v_declName_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2069_, v_declName_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec(v_declName_2070_);
lean_dec_ref(v_ext_2069_);
return v_res_2073_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2074_, lean_object* v_declName_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2074_, v_declName_2075_, v_a_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2074_ = stack[0].m_obj;
lean_object* v_declName_2075_ = stack[1].m_obj;
lean_object* v_a_2076_ = stack[2].m_obj;
lean_object* v_a_2077_ = stack[3].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2074_, v_declName_2075_, v_a_2076_, v_a_2077_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2081_, lean_object* v_declName_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2081_, v_declName_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_declName_2082_);
lean_dec_ref(v_ext_2081_);
return v_res_2086_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2088_, v_x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2088_ = stack[1].m_obj;
lean_object* v_x_2089_ = stack[2].m_obj;
uint8_t v_res_2091_;
v_res_2091_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_box(0), v_x_2088_, v_x_2089_);
stack->m_num = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
uint8_t v_res_2095_; lean_object* v_r_2096_; 
v_res_2095_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2092_, v_x_2093_, v_x_2094_);
lean_dec(v_x_2094_);
lean_dec_ref(v_x_2093_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2097_, lean_object* v_x_2098_, size_t v_x_2099_, lean_object* v_x_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2098_, v_x_2099_, v_x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2098_ = stack[1].m_obj;
size_t v_x_2099_ = stack[2].m_num;
lean_object* v_x_2100_ = stack[3].m_obj;
uint8_t v_res_2102_;
v_res_2102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_box(0), v_x_2098_, v_x_2099_, v_x_2100_);
stack->m_num = v_res_2102_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
size_t v_x_470__boxed_2107_; uint8_t v_res_2108_; lean_object* v_r_2109_; 
v_x_470__boxed_2107_ = lean_unbox_usize(v_x_2105_);
lean_dec(v_x_2105_);
v_res_2108_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2103_, v_x_2104_, v_x_470__boxed_2107_, v_x_2106_);
lean_dec(v_x_2106_);
lean_dec_ref(v_x_2104_);
v_r_2109_ = lean_box(v_res_2108_);
return v_r_2109_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2110_, lean_object* v_keys_2111_, lean_object* v_vals_2112_, lean_object* v_heq_2113_, lean_object* v_i_2114_, lean_object* v_k_2115_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2111_, v_i_2114_, v_k_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2111_ = stack[1].m_obj;
lean_object* v_vals_2112_ = stack[2].m_obj;
lean_object* v_i_2114_ = stack[4].m_obj;
lean_object* v_k_2115_ = stack[5].m_obj;
uint8_t v_res_2117_;
v_res_2117_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_box(0), v_keys_2111_, v_vals_2112_, lean_box(0), v_i_2114_, v_k_2115_);
stack->m_num = v_res_2117_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2118_, lean_object* v_keys_2119_, lean_object* v_vals_2120_, lean_object* v_heq_2121_, lean_object* v_i_2122_, lean_object* v_k_2123_){
_start:
{
uint8_t v_res_2124_; lean_object* v_r_2125_; 
v_res_2124_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2118_, v_keys_2119_, v_vals_2120_, v_heq_2121_, v_i_2122_, v_k_2123_);
lean_dec(v_k_2123_);
lean_dec_ref(v_vals_2120_);
lean_dec_ref(v_keys_2119_);
v_r_2125_ = lean_box(v_res_2124_);
return v_r_2125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2126_, lean_object* v_declName_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v_ext_2132_; lean_object* v_toEnvExtension_2133_; lean_object* v_env_2134_; lean_object* v_asyncMode_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v_inj_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2130_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2131_ = lean_st_ref_get(v_a_2128_);
v_ext_2132_ = lean_ctor_get(v_ext_2126_, 1);
v_toEnvExtension_2133_ = lean_ctor_get(v_ext_2132_, 0);
v_env_2134_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2131_);
v_asyncMode_2135_ = lean_ctor_get(v_toEnvExtension_2133_, 2);
v___x_2136_ = 0;
v___x_2137_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2130_, v_ext_2126_, v_env_2134_, v_asyncMode_2135_, v___x_2136_);
v_inj_2138_ = lean_ctor_get(v___x_2137_, 4);
lean_inc_ref(v_inj_2138_);
lean_dec(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_declName_2127_);
v___x_2140_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2138_, v___x_2139_);
lean_dec_ref_known(v___x_2139_, 1);
lean_dec_ref(v_inj_2138_);
v___x_2141_ = lean_box(v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2126_ = stack[0].m_obj;
lean_object* v_declName_2127_ = stack[1].m_obj;
lean_object* v_a_2128_ = stack[2].m_obj;
lean_object* v_res_2143_;
v_res_2143_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2126_, v_declName_2127_, v_a_2128_);
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2144_, lean_object* v_declName_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2144_, v_declName_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_ext_2144_);
return v_res_2148_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2149_, lean_object* v_declName_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2149_, v_declName_2150_, v_a_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2149_ = stack[0].m_obj;
lean_object* v_declName_2150_ = stack[1].m_obj;
lean_object* v_a_2151_ = stack[2].m_obj;
lean_object* v_a_2152_ = stack[3].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2149_, v_declName_2150_, v_a_2151_, v_a_2152_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2156_, lean_object* v_declName_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2156_, v_declName_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec_ref(v_ext_2156_);
return v_res_2161_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2162_, lean_object* v_declName_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_ext_2168_; lean_object* v_toEnvExtension_2169_; lean_object* v_env_2170_; lean_object* v_asyncMode_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v_funCC_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2166_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2167_ = lean_st_ref_get(v_a_2164_);
v_ext_2168_ = lean_ctor_get(v_ext_2162_, 1);
v_toEnvExtension_2169_ = lean_ctor_get(v_ext_2168_, 0);
v_env_2170_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2170_);
lean_dec(v___x_2167_);
v_asyncMode_2171_ = lean_ctor_get(v_toEnvExtension_2169_, 2);
v___x_2172_ = 0;
v___x_2173_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2166_, v_ext_2162_, v_env_2170_, v_asyncMode_2171_, v___x_2172_);
v_funCC_2174_ = lean_ctor_get(v___x_2173_, 2);
lean_inc(v_funCC_2174_);
lean_dec(v___x_2173_);
v___x_2175_ = l_Lean_NameSet_contains(v_funCC_2174_, v_declName_2163_);
lean_dec(v_funCC_2174_);
v___x_2176_ = lean_box(v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2162_ = stack[0].m_obj;
lean_object* v_declName_2163_ = stack[1].m_obj;
lean_object* v_a_2164_ = stack[2].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2162_, v_declName_2163_, v_a_2164_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2179_, lean_object* v_declName_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2179_, v_declName_2180_, v_a_2181_);
lean_dec(v_a_2181_);
lean_dec(v_declName_2180_);
lean_dec_ref(v_ext_2179_);
return v_res_2183_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2184_, lean_object* v_declName_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2184_, v_declName_2185_, v_a_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2184_ = stack[0].m_obj;
lean_object* v_declName_2185_ = stack[1].m_obj;
lean_object* v_a_2186_ = stack[2].m_obj;
lean_object* v_a_2187_ = stack[3].m_obj;
lean_object* v_res_2190_;
v_res_2190_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2184_, v_declName_2185_, v_a_2186_, v_a_2187_);
stack->m_obj
 = v_res_2190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2191_, lean_object* v_declName_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2191_, v_declName_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_declName_2192_);
lean_dec_ref(v_ext_2191_);
return v_res_2196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2221_ = l_Lean_mkAtom(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2224_ = lean_array_push(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2234_ = l_Lean_mkAtom(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2237_ = lean_array_push(v___x_2236_, v___x_2235_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2240_ = lean_box(2);
v___x_2241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2239_);
lean_ctor_set(v___x_2241_, 2, v___x_2238_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2244_ = lean_array_push(v___x_2243_, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2247_ = lean_box(2);
v___x_2248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2246_);
lean_ctor_set(v___x_2248_, 2, v___x_2245_);
return v___x_2248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2251_ = lean_array_push(v___x_2250_, v___x_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2254_ = lean_box(2);
v___x_2255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2253_);
lean_ctor_set(v___x_2255_, 2, v___x_2252_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2258_ = lean_array_push(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2261_ = lean_box(2);
v___x_2262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2260_);
lean_ctor_set(v___x_2262_, 2, v___x_2259_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2265_ = lean_array_push(v___x_2264_, v___x_2263_);
return v___x_2265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2268_ = lean_box(2);
v___x_2269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2267_);
lean_ctor_set(v___x_2269_, 2, v___x_2266_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2270_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2271_, lean_object* v_ext_2272_, lean_object* v_____r_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = 0;
lean_inc(v_declName_2271_);
v___x_2280_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2271_, v___x_2279_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; uint8_t v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = lean_unbox(v_a_2281_);
lean_dec(v_a_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v_a_2284_; uint8_t v___x_2285_; 
v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2272_, v_declName_2271_, v___y_2277_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2283_);
v___x_2285_ = lean_unbox(v_a_2284_);
lean_dec(v_a_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v_a_2287_; uint8_t v___x_2288_; 
lean_inc(v_declName_2271_);
v___x_2286_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2272_, v_declName_2271_, v___y_2277_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
v___x_2288_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v_a_2290_; uint8_t v___x_2291_; 
v___x_2289_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2272_, v_declName_2271_, v___y_2277_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = lean_unbox(v_a_2290_);
lean_dec(v_a_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2272_, v_declName_2271_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2292_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2272_, v_declName_2271_, v___y_2276_, v___y_2277_);
return v___x_2293_;
}
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2272_, v_declName_2271_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2294_;
}
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2272_, v_declName_2271_, v___y_2276_, v___y_2277_);
return v___x_2295_;
}
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2272_, v_declName_2271_, v___y_2276_, v___y_2277_);
return v___x_2296_;
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v_ext_2272_);
lean_dec(v_declName_2271_);
v_a_2297_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2280_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2280_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2271_ = stack[0].m_obj;
lean_object* v_ext_2272_ = stack[1].m_obj;
lean_object* v_____r_2273_ = stack[2].m_obj;
lean_object* v___y_2274_ = stack[3].m_obj;
lean_object* v___y_2275_ = stack[4].m_obj;
lean_object* v___y_2276_ = stack[5].m_obj;
lean_object* v___y_2277_ = stack[6].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2271_, v_ext_2272_, v_____r_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2306_, lean_object* v_ext_2307_, lean_object* v_____r_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2306_, v_ext_2307_, v_____r_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2314_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_env_2322_; uint8_t v___x_2323_; lean_object* v_env_2324_; lean_object* v___x_2325_; lean_object* v_toCold_2326_; lean_object* v_mctx_2327_; lean_object* v_lctx_2328_; lean_object* v_options_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2321_ = lean_st_ref_get(v___y_2319_);
v_env_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_ref(v_env_2322_);
lean_dec(v___x_2321_);
v___x_2323_ = 0;
v_env_2324_ = l_Lean_Environment_setRecordingDeps(v_env_2322_, v___x_2323_);
v___x_2325_ = lean_st_ref_get(v___y_2317_);
v_toCold_2326_ = lean_ctor_get(v___y_2318_, 0);
v_mctx_2327_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_mctx_2327_);
lean_dec(v___x_2325_);
v_lctx_2328_ = lean_ctor_get(v___y_2316_, 2);
v_options_2329_ = lean_ctor_get(v_toCold_2326_, 2);
lean_inc_ref(v_options_2329_);
lean_inc_ref(v_lctx_2328_);
v___x_2330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2330_, 0, v_env_2324_);
lean_ctor_set(v___x_2330_, 1, v_mctx_2327_);
lean_ctor_set(v___x_2330_, 2, v_lctx_2328_);
lean_ctor_set(v___x_2330_, 3, v_options_2329_);
v___x_2331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v_msgData_2315_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2315_ = stack[0].m_obj;
lean_object* v___y_2316_ = stack[1].m_obj;
lean_object* v___y_2317_ = stack[2].m_obj;
lean_object* v___y_2318_ = stack[3].m_obj;
lean_object* v___y_2319_ = stack[4].m_obj;
lean_object* v_res_2333_;
v_res_2333_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
stack->m_obj
 = v_res_2333_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2340_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_ref_2347_; lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
v_ref_2347_ = lean_ctor_get(v___y_2344_, 2);
v___x_2348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
lean_inc(v_ref_2347_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_ref_2347_);
lean_ctor_set(v___x_2353_, 1, v_a_2349_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 1);
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2341_ = stack[0].m_obj;
lean_object* v___y_2342_ = stack[1].m_obj;
lean_object* v___y_2343_ = stack[2].m_obj;
lean_object* v___y_2344_ = stack[3].m_obj;
lean_object* v___y_2345_ = stack[4].m_obj;
lean_object* v_res_2358_;
v_res_2358_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
stack->m_obj
 = v_res_2358_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2365_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2372_; uint64_t v___x_2373_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2376_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set_uint64(v___x_2376_, sizeof(void*)*1, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2379_ = lean_box(1);
v___x_2380_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v___x_2380_);
lean_ctor_set(v___x_2382_, 2, v___x_2379_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
lean_ctor_set(v___x_2388_, 2, v___x_2387_);
lean_ctor_set(v___x_2388_, 3, v___x_2387_);
lean_ctor_set(v___x_2388_, 4, v___x_2386_);
lean_ctor_set(v___x_2388_, 5, v___x_2386_);
lean_ctor_set(v___x_2388_, 6, v___x_2386_);
lean_ctor_set(v___x_2388_, 7, v___x_2386_);
lean_ctor_set(v___x_2388_, 8, v___x_2386_);
lean_ctor_set(v___x_2388_, 9, v___x_2386_);
lean_ctor_set(v___x_2388_, 10, v___x_2386_);
lean_ctor_set(v___x_2388_, 11, v___x_2385_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
lean_ctor_set(v___x_2390_, 2, v___x_2389_);
lean_ctor_set(v___x_2390_, 3, v___x_2389_);
lean_ctor_set(v___x_2390_, 4, v___x_2389_);
lean_ctor_set(v___x_2390_, 5, v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
lean_ctor_set(v___x_2392_, 2, v___x_2391_);
lean_ctor_set(v___x_2392_, 3, v___x_2391_);
lean_ctor_set(v___x_2392_, 4, v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
return v___x_2401_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_2402_, lean_object* v___x_2403_, uint8_t v_showInfo_2404_, lean_object* v_attrName_2405_, lean_object* v_declName_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___y_2425_; 
v___x_2410_ = 1;
v___x_2411_ = 0;
v___x_2412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2413_ = lean_unsigned_to_nat(0u);
v___x_2414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_2417_ = lean_box(0);
lean_inc(v___x_2403_);
v___x_2418_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2418_, 0, v___x_2412_);
lean_ctor_set(v___x_2418_, 1, v___x_2403_);
lean_ctor_set(v___x_2418_, 2, v___x_2415_);
lean_ctor_set(v___x_2418_, 3, v___x_2416_);
lean_ctor_set(v___x_2418_, 4, v___x_2417_);
lean_ctor_set(v___x_2418_, 5, v___x_2413_);
lean_ctor_set(v___x_2418_, 6, v___x_2417_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7, v___x_2411_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 1, v___x_2411_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 2, v___x_2411_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 3, v___x_2410_);
v___x_2419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2419_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
lean_ctor_set(v___x_2422_, 2, v___x_2403_);
lean_ctor_set(v___x_2422_, 3, v___x_2414_);
lean_ctor_set(v___x_2422_, 4, v___x_2421_);
v___x_2423_ = lean_st_mk_ref(v___x_2422_);
if (v_showInfo_2404_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_attrName_2405_);
v___x_2435_ = lean_box(0);
v___x_2436_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2406_, v_ext_2402_, v___x_2435_, v___x_2418_, v___x_2423_, v___y_2407_, v___y_2408_);
lean_dec_ref_known(v___x_2418_, 7);
v___y_2425_ = v___x_2436_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec(v_declName_2406_);
lean_dec_ref(v_ext_2402_);
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_2438_ = l_Lean_MessageData_ofName(v_attrName_2405_);
lean_inc_ref(v___x_2438_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___x_2438_);
v___x_2443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2444_, v___x_2418_, v___x_2423_, v___y_2407_, v___y_2408_);
lean_dec_ref_known(v___x_2418_, 7);
v___y_2425_ = v___x_2445_;
goto v___jp_2424_;
}
v___jp_2424_:
{
if (lean_obj_tag(v___y_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2434_; 
v_a_2426_ = lean_ctor_get(v___y_2425_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___y_2425_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2428_ = v___y_2425_;
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___y_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = lean_st_ref_get(v___x_2423_);
lean_dec(v___x_2423_);
lean_dec(v___x_2430_);
if (v_isShared_2429_ == 0)
{
v___x_2432_ = v___x_2428_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2426_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_dec(v___x_2423_);
return v___y_2425_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2402_ = stack[0].m_obj;
lean_object* v___x_2403_ = stack[1].m_obj;
uint8_t v_showInfo_2404_ = stack[2].m_num;
lean_object* v_attrName_2405_ = stack[3].m_obj;
lean_object* v_declName_2406_ = stack[4].m_obj;
lean_object* v___y_2407_ = stack[5].m_obj;
lean_object* v___y_2408_ = stack[6].m_obj;
lean_object* v_res_2446_;
v_res_2446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_2402_, v___x_2403_, v_showInfo_2404_, v_attrName_2405_, v_declName_2406_, v___y_2407_, v___y_2408_);
stack->m_obj
 = v_res_2446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_2447_, lean_object* v___x_2448_, lean_object* v_showInfo_2449_, lean_object* v_attrName_2450_, lean_object* v_declName_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v_showInfo_boxed_2455_; lean_object* v_res_2456_; 
v_showInfo_boxed_2455_ = lean_unbox(v_showInfo_2449_);
v_res_2456_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_2447_, v___x_2448_, v_showInfo_boxed_2455_, v_attrName_2450_, v_declName_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2456_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2459_, uint8_t v_attrKind_2460_, uint8_t v_showInfo_2461_, uint8_t v_minIndexable_2462_, lean_object* v_as_x27_2463_, lean_object* v_b_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
if (lean_obj_tag(v_as_x27_2463_) == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v_ext_2459_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_b_2464_);
return v___x_2470_;
}
else
{
lean_object* v_head_2471_; lean_object* v_tail_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_head_2471_ = lean_ctor_get(v_as_x27_2463_, 0);
v_tail_2472_ = lean_ctor_get(v_as_x27_2463_, 1);
v___x_2473_ = lean_box(0);
v___x_2474_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2468_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2471_);
lean_inc_ref(v_ext_2459_);
v___x_2477_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2459_, v_head_2471_, v_attrKind_2460_, v___x_2476_, v_a_2475_, v_showInfo_2461_, v_minIndexable_2462_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_dec_ref_known(v___x_2477_, 1);
v_as_x27_2463_ = v_tail_2472_;
v_b_2464_ = v___x_2473_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2459_);
return v___x_2477_;
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_ext_2459_);
v_a_2479_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2474_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2474_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2459_ = stack[0].m_obj;
uint8_t v_attrKind_2460_ = stack[1].m_num;
uint8_t v_showInfo_2461_ = stack[2].m_num;
uint8_t v_minIndexable_2462_ = stack[3].m_num;
lean_object* v_as_x27_2463_ = stack[4].m_obj;
lean_object* v_b_2464_ = stack[5].m_obj;
lean_object* v___y_2465_ = stack[6].m_obj;
lean_object* v___y_2466_ = stack[7].m_obj;
lean_object* v___y_2467_ = stack[8].m_obj;
lean_object* v___y_2468_ = stack[9].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2459_, v_attrKind_2460_, v_showInfo_2461_, v_minIndexable_2462_, v_as_x27_2463_, v_b_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2488_, lean_object* v_attrKind_2489_, lean_object* v_showInfo_2490_, lean_object* v_minIndexable_2491_, lean_object* v_as_x27_2492_, lean_object* v_b_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_attrKind_boxed_2499_; uint8_t v_showInfo_boxed_2500_; uint8_t v_minIndexable_boxed_2501_; lean_object* v_res_2502_; 
v_attrKind_boxed_2499_ = lean_unbox(v_attrKind_2489_);
v_showInfo_boxed_2500_ = lean_unbox(v_showInfo_2490_);
v_minIndexable_boxed_2501_ = lean_unbox(v_minIndexable_2491_);
v_res_2502_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2488_, v_attrKind_boxed_2499_, v_showInfo_boxed_2500_, v_minIndexable_boxed_2501_, v_as_x27_2492_, v_b_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v_as_x27_2492_);
return v_res_2502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2511_ = l_Lean_stringToMessageData(v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
return v___x_2532_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_2533_, uint8_t v___x_2534_, uint8_t v_attrKind_2535_, lean_object* v_stx_2536_, lean_object* v_ext_2537_, uint8_t v_showInfo_2538_, uint8_t v_minIndexable_2539_, lean_object* v_attrName_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2536_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
switch(lean_obj_tag(v_a_2571_))
{
case 0:
{
lean_object* v_k_2572_; 
lean_dec(v_attrName_2540_);
lean_dec(v_stx_2536_);
v_k_2572_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_k_2572_);
lean_dec_ref_known(v_a_2571_, 1);
if (lean_obj_tag(v_k_2572_) == 9)
{
lean_object* v___x_2573_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_declName_2533_);
v___x_2573_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2543_, v___y_2544_);
return v___x_2573_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2544_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2537_, v_declName_2533_, v_attrKind_2535_, v_k_2572_, v_a_2575_, v_showInfo_2538_, v_minIndexable_2539_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2576_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_k_2572_);
lean_dec_ref(v_ext_2537_);
lean_dec(v_declName_2533_);
v_a_2577_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2574_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2574_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2585_; lean_object* v___x_2586_; 
lean_dec(v_attrName_2540_);
lean_dec(v_stx_2536_);
v_eager_2585_ = lean_ctor_get_uint8(v_a_2571_, 0);
lean_dec_ref_known(v_a_2571_, 0);
v___x_2586_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2537_, v_declName_2533_, v_eager_2585_, v_attrKind_2535_, v___y_2543_, v___y_2544_);
return v___x_2586_;
}
case 2:
{
lean_object* v___x_2587_; 
lean_dec(v_stx_2536_);
lean_inc(v_declName_2533_);
v___x_2587_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2533_, v___x_2534_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
if (lean_obj_tag(v_a_2588_) == 1)
{
lean_object* v_val_2589_; lean_object* v_ctors_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_attrName_2540_);
lean_dec(v_declName_2533_);
v_val_2589_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_val_2589_);
lean_dec_ref_known(v_a_2588_, 1);
v_ctors_2590_ = lean_ctor_get(v_val_2589_, 4);
lean_inc(v_ctors_2590_);
lean_dec(v_val_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2537_, v_attrKind_2535_, v_showInfo_2538_, v_minIndexable_2539_, v_ctors_2590_, v___x_2591_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v_ctors_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v___x_2592_, 0);
lean_dec(v_unused_2600_);
v___x_2594_ = v___x_2592_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v___x_2592_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2591_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
return v___x_2592_;
}
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v_a_2588_);
lean_dec_ref(v_ext_2537_);
v___x_2601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2602_ = l_Lean_MessageData_ofName(v_attrName_2540_);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_MessageData_ofConstName(v_declName_2533_, v___x_2534_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2609_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2610_;
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_attrName_2540_);
lean_dec_ref(v_ext_2537_);
lean_dec(v_declName_2533_);
v_a_2611_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2587_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2587_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
case 3:
{
lean_object* v___x_2619_; 
lean_dec(v_attrName_2540_);
lean_inc(v_declName_2533_);
v___x_2619_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2533_, v___x_2534_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
if (lean_obj_tag(v_a_2620_) == 1)
{
lean_object* v_val_2621_; lean_object* v___x_2622_; 
lean_dec(v_stx_2536_);
lean_dec(v_declName_2533_);
v_val_2621_ = lean_ctor_get(v_a_2620_, 0);
lean_inc_n(v_val_2621_, 2);
lean_dec_ref_known(v_a_2620_, 1);
lean_inc_ref(v_ext_2537_);
v___x_2622_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2537_, v_val_2621_, v___x_2534_, v_attrKind_2535_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2623_; 
lean_dec_ref_known(v___x_2622_, 1);
v___x_2623_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2621_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2644_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2644_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
if (lean_obj_tag(v_a_2624_) == 1)
{
lean_object* v_val_2628_; lean_object* v_ctors_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_del_object(v___x_2626_);
v_val_2628_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v_a_2624_, 1);
v_ctors_2629_ = lean_ctor_get(v_val_2628_, 4);
lean_inc(v_ctors_2629_);
lean_dec(v_val_2628_);
v___x_2630_ = lean_box(0);
v___x_2631_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2537_, v_attrKind_2535_, v_showInfo_2538_, v_minIndexable_2539_, v_ctors_2629_, v___x_2630_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v_ctors_2629_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v___x_2631_, 0);
lean_dec(v_unused_2639_);
v___x_2633_ = v___x_2631_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_dec(v___x_2631_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2630_);
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2630_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
return v___x_2631_;
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
lean_dec(v_a_2624_);
lean_dec_ref(v_ext_2537_);
v___x_2640_ = lean_box(0);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2640_);
v___x_2642_ = v___x_2626_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_ext_2537_);
v_a_2645_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2623_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2623_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_dec(v_val_2621_);
lean_dec_ref(v_ext_2537_);
return v___x_2622_;
}
}
else
{
lean_object* v___x_2653_; 
lean_dec(v_a_2620_);
v___x_2653_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2544_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2537_, v_stx_2536_, v_declName_2533_, v_attrKind_2535_, v_a_2654_, v_minIndexable_2539_, v_showInfo_2538_, v___x_2534_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
lean_dec(v_declName_2533_);
v_a_2656_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2653_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2653_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
lean_dec(v_declName_2533_);
v_a_2664_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2619_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2619_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
case 4:
{
lean_object* v___x_2672_; 
lean_dec(v_attrName_2540_);
lean_dec(v_stx_2536_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2537_, v_declName_2533_, v_attrKind_2535_, v___y_2543_, v___y_2544_);
return v___x_2672_;
}
case 5:
{
lean_object* v_prio_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
v_prio_2673_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_prio_2673_);
lean_dec_ref_known(v_a_2571_, 1);
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2675_ = lean_name_eq(v_attrName_2540_, v___x_2674_);
lean_dec(v_attrName_2540_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec(v_prio_2673_);
lean_dec(v_declName_2533_);
v___x_2676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2677_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2676_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2533_, v_attrKind_2535_, v_prio_2673_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2678_;
}
}
case 6:
{
lean_object* v___x_2679_; 
lean_dec(v_attrName_2540_);
lean_dec(v_stx_2536_);
v___x_2679_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2537_, v_declName_2533_, v_attrKind_2535_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2679_;
}
case 7:
{
lean_object* v___x_2680_; 
lean_dec(v_attrName_2540_);
lean_dec(v_stx_2536_);
v___x_2680_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2537_, v_declName_2533_, v_attrKind_2535_, v___y_2543_, v___y_2544_);
return v___x_2680_;
}
case 8:
{
uint8_t v_post_2681_; uint8_t v_inv_2682_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
v_post_2681_ = lean_ctor_get_uint8(v_a_2571_, 0);
v_inv_2682_ = lean_ctor_get_uint8(v_a_2571_, 1);
lean_dec_ref_known(v_a_2571_, 0);
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2692_ = lean_name_eq(v_attrName_2540_, v___x_2691_);
lean_dec(v_attrName_2540_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v_declName_2533_);
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2694_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2693_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2694_;
}
else
{
v___y_2684_ = v___y_2541_;
v___y_2685_ = v___y_2542_;
v___y_2686_ = v___y_2543_;
v___y_2687_ = v___y_2544_;
goto v___jp_2683_;
}
v___jp_2683_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = l_Lean_Meta_Grind_normExt;
v___x_2689_ = lean_unsigned_to_nat(1000u);
v___x_2690_ = l_Lean_Meta_addSimpTheorem(v___x_2688_, v_declName_2533_, v_post_2681_, v_inv_2682_, v_attrKind_2535_, v___x_2689_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2690_;
}
}
case 9:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2696_ = lean_name_eq(v_attrName_2540_, v___x_2695_);
lean_dec(v_attrName_2540_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec(v_declName_2533_);
v___x_2697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2698_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2697_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2698_;
}
else
{
goto v___jp_2546_;
}
}
case 10:
{
uint8_t v_fallback_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
v_fallback_2699_ = lean_ctor_get_uint8(v_a_2571_, 0);
lean_dec_ref_known(v_a_2571_, 0);
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2701_ = lean_name_eq(v_attrName_2540_, v___x_2700_);
lean_dec(v_attrName_2540_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec(v_declName_2533_);
v___x_2702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2703_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2702_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2703_;
}
else
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2533_, v_attrKind_2535_, v_fallback_2699_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2704_;
}
}
default: 
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2706_ = lean_name_eq(v_attrName_2540_, v___x_2705_);
lean_dec(v_attrName_2540_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v_declName_2533_);
v___x_2707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2708_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2707_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2533_, v_attrKind_2535_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_attrName_2540_);
lean_dec_ref(v_ext_2537_);
lean_dec(v_stx_2536_);
lean_dec(v_declName_2533_);
v_a_2710_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2570_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2570_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
v___jp_2546_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = l_Lean_Meta_Grind_normExt;
v___x_2548_ = lean_unsigned_to_nat(1000u);
v___x_2549_ = l_Lean_Meta_addDeclToUnfold(v___x_2547_, v_declName_2533_, v___x_2534_, v___x_2534_, v___x_2548_, v_attrKind_2535_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2561_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2561_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2561_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_unbox(v_a_2550_);
lean_dec(v_a_2550_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_del_object(v___x_2552_);
v___x_2555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2556_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2555_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_box(0);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2557_);
v___x_2559_ = v___x_2552_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2549_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2549_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2533_ = stack[0].m_obj;
uint8_t v___x_2534_ = stack[1].m_num;
uint8_t v_attrKind_2535_ = stack[2].m_num;
lean_object* v_stx_2536_ = stack[3].m_obj;
lean_object* v_ext_2537_ = stack[4].m_obj;
uint8_t v_showInfo_2538_ = stack[5].m_num;
uint8_t v_minIndexable_2539_ = stack[6].m_num;
lean_object* v_attrName_2540_ = stack[7].m_obj;
lean_object* v___y_2541_ = stack[8].m_obj;
lean_object* v___y_2542_ = stack[9].m_obj;
lean_object* v___y_2543_ = stack[10].m_obj;
lean_object* v___y_2544_ = stack[11].m_obj;
lean_object* v_res_2718_;
v_res_2718_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_2533_, v___x_2534_, v_attrKind_2535_, v_stx_2536_, v_ext_2537_, v_showInfo_2538_, v_minIndexable_2539_, v_attrName_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
stack->m_obj
 = v_res_2718_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_2719_, lean_object* v___x_2720_, lean_object* v_attrKind_2721_, lean_object* v_stx_2722_, lean_object* v_ext_2723_, lean_object* v_showInfo_2724_, lean_object* v_minIndexable_2725_, lean_object* v_attrName_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v___x_15469__boxed_2732_; uint8_t v_attrKind_boxed_2733_; uint8_t v_showInfo_boxed_2734_; uint8_t v_minIndexable_boxed_2735_; lean_object* v_res_2736_; 
v___x_15469__boxed_2732_ = lean_unbox(v___x_2720_);
v_attrKind_boxed_2733_ = lean_unbox(v_attrKind_2721_);
v_showInfo_boxed_2734_ = lean_unbox(v_showInfo_2724_);
v_minIndexable_boxed_2735_ = lean_unbox(v_minIndexable_2725_);
v_res_2736_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_2719_, v___x_15469__boxed_2732_, v_attrKind_boxed_2733_, v_stx_2722_, v_ext_2723_, v_showInfo_boxed_2734_, v_minIndexable_boxed_2735_, v_attrName_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2736_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2737_; double v___x_2738_; 
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = lean_float_of_nat(v___x_2737_);
return v___x_2738_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2742_, lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_ref_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2796_; 
v_ref_2749_ = lean_ctor_get(v___y_2746_, 2);
v___x_2750_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2796_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2796_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_traceState_2756_; lean_object* v_env_2757_; lean_object* v_nextMacroScope_2758_; lean_object* v_ngen_2759_; lean_object* v_auxDeclNGen_2760_; lean_object* v_cache_2761_; lean_object* v_recordedDeps_2762_; lean_object* v_messages_2763_; lean_object* v_infoState_2764_; lean_object* v_snapshotTasks_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2795_; 
v___x_2755_ = lean_st_ref_take(v___y_2747_);
v_traceState_2756_ = lean_ctor_get(v___x_2755_, 4);
v_env_2757_ = lean_ctor_get(v___x_2755_, 0);
v_nextMacroScope_2758_ = lean_ctor_get(v___x_2755_, 1);
v_ngen_2759_ = lean_ctor_get(v___x_2755_, 2);
v_auxDeclNGen_2760_ = lean_ctor_get(v___x_2755_, 3);
v_cache_2761_ = lean_ctor_get(v___x_2755_, 5);
v_recordedDeps_2762_ = lean_ctor_get(v___x_2755_, 6);
v_messages_2763_ = lean_ctor_get(v___x_2755_, 7);
v_infoState_2764_ = lean_ctor_get(v___x_2755_, 8);
v_snapshotTasks_2765_ = lean_ctor_get(v___x_2755_, 9);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2767_ = v___x_2755_;
v_isShared_2768_ = v_isSharedCheck_2795_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_snapshotTasks_2765_);
lean_inc(v_infoState_2764_);
lean_inc(v_messages_2763_);
lean_inc(v_recordedDeps_2762_);
lean_inc(v_cache_2761_);
lean_inc(v_traceState_2756_);
lean_inc(v_auxDeclNGen_2760_);
lean_inc(v_ngen_2759_);
lean_inc(v_nextMacroScope_2758_);
lean_inc(v_env_2757_);
lean_dec(v___x_2755_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2795_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint64_t v_tid_2769_; lean_object* v_traces_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2794_; 
v_tid_2769_ = lean_ctor_get_uint64(v_traceState_2756_, sizeof(void*)*1);
v_traces_2770_ = lean_ctor_get(v_traceState_2756_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_traceState_2756_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2772_ = v_traceState_2756_;
v_isShared_2773_ = v_isSharedCheck_2794_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_traces_2770_);
lean_dec(v_traceState_2756_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2794_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; double v___x_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_box(0);
v___x_2776_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2777_ = 0;
v___x_2778_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2779_, 0, v_cls_2742_);
lean_ctor_set(v___x_2779_, 1, v___x_2775_);
lean_ctor_set(v___x_2779_, 2, v___x_2778_);
lean_ctor_set_float(v___x_2779_, sizeof(void*)*3, v___x_2776_);
lean_ctor_set_float(v___x_2779_, sizeof(void*)*3 + 8, v___x_2776_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*3 + 16, v___x_2777_);
v___x_2780_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2781_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v_a_2751_);
lean_ctor_set(v___x_2781_, 2, v___x_2780_);
lean_inc(v_ref_2749_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_ref_2749_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_PersistentArray_push___redArg(v_traces_2770_, v___x_2782_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2783_);
v___x_2785_ = v___x_2772_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2783_);
lean_ctor_set_uint64(v_reuseFailAlloc_2793_, sizeof(void*)*1, v_tid_2769_);
v___x_2785_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2787_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 4, v___x_2785_);
v___x_2787_ = v___x_2767_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_env_2757_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_nextMacroScope_2758_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_ngen_2759_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_auxDeclNGen_2760_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2792_, 5, v_cache_2761_);
lean_ctor_set(v_reuseFailAlloc_2792_, 6, v_recordedDeps_2762_);
lean_ctor_set(v_reuseFailAlloc_2792_, 7, v_messages_2763_);
lean_ctor_set(v_reuseFailAlloc_2792_, 8, v_infoState_2764_);
lean_ctor_set(v_reuseFailAlloc_2792_, 9, v_snapshotTasks_2765_);
v___x_2787_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = lean_st_ref_put(v___y_2747_, v___x_2787_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2774_);
v___x_2790_ = v___x_2753_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2774_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2742_ = stack[0].m_obj;
lean_object* v_msg_2743_ = stack[1].m_obj;
lean_object* v___y_2744_ = stack[2].m_obj;
lean_object* v___y_2745_ = stack[3].m_obj;
lean_object* v___y_2746_ = stack[4].m_obj;
lean_object* v___y_2747_ = stack[5].m_obj;
lean_object* v_res_2797_;
v_res_2797_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2742_, v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
stack->m_obj
 = v_res_2797_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2798_, v_msg_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2805_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2806_, lean_object* v_i_2807_, lean_object* v_k_2808_){
_start:
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = lean_array_get_size(v_keys_2806_);
v___x_2810_ = lean_nat_dec_lt(v_i_2807_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_dec(v_i_2807_);
return v___x_2810_;
}
else
{
lean_object* v_k_x27_2811_; uint8_t v___x_2812_; 
v_k_x27_2811_ = lean_array_fget_borrowed(v_keys_2806_, v_i_2807_);
v___x_2812_ = l_Lean_instBEqExtraModUse_beq(v_k_2808_, v_k_x27_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_unsigned_to_nat(1u);
v___x_2814_ = lean_nat_add(v_i_2807_, v___x_2813_);
lean_dec(v_i_2807_);
v_i_2807_ = v___x_2814_;
goto _start;
}
else
{
lean_dec(v_i_2807_);
return v___x_2810_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2806_ = stack[0].m_obj;
lean_object* v_i_2807_ = stack[1].m_obj;
lean_object* v_k_2808_ = stack[2].m_obj;
uint8_t v_res_2816_;
v_res_2816_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2806_, v_i_2807_, v_k_2808_);
stack->m_num = v_res_2816_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2817_, lean_object* v_i_2818_, lean_object* v_k_2819_){
_start:
{
uint8_t v_res_2820_; lean_object* v_r_2821_; 
v_res_2820_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2817_, v_i_2818_, v_k_2819_);
lean_dec_ref(v_k_2819_);
lean_dec_ref(v_keys_2817_);
v_r_2821_ = lean_box(v_res_2820_);
return v_r_2821_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2822_, size_t v_x_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2822_) == 0)
{
lean_object* v_es_2825_; lean_object* v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; lean_object* v_j_2829_; lean_object* v___x_2830_; 
v_es_2825_ = lean_ctor_get(v_x_2822_, 0);
v___x_2826_ = lean_box(2);
v___x_2827_ = ((size_t)31ULL);
v___x_2828_ = lean_usize_land(v_x_2823_, v___x_2827_);
v_j_2829_ = lean_usize_to_nat(v___x_2828_);
v___x_2830_ = lean_array_get_borrowed(v___x_2826_, v_es_2825_, v_j_2829_);
lean_dec(v_j_2829_);
switch(lean_obj_tag(v___x_2830_))
{
case 0:
{
lean_object* v_key_2831_; uint8_t v___x_2832_; 
v_key_2831_ = lean_ctor_get(v___x_2830_, 0);
v___x_2832_ = l_Lean_instBEqExtraModUse_beq(v_x_2824_, v_key_2831_);
return v___x_2832_;
}
case 1:
{
lean_object* v_node_2833_; size_t v___x_2834_; size_t v___x_2835_; 
v_node_2833_ = lean_ctor_get(v___x_2830_, 0);
v___x_2834_ = ((size_t)5ULL);
v___x_2835_ = lean_usize_shift_right(v_x_2823_, v___x_2834_);
v_x_2822_ = v_node_2833_;
v_x_2823_ = v___x_2835_;
goto _start;
}
default: 
{
uint8_t v___x_2837_; 
v___x_2837_ = 0;
return v___x_2837_;
}
}
}
else
{
lean_object* v_ks_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_ks_2838_ = lean_ctor_get(v_x_2822_, 0);
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2838_, v___x_2839_, v_x_2824_);
return v___x_2840_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2822_ = stack[0].m_obj;
size_t v_x_2823_ = stack[1].m_num;
lean_object* v_x_2824_ = stack[2].m_obj;
uint8_t v_res_2841_;
v_res_2841_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2822_, v_x_2823_, v_x_2824_);
stack->m_num = v_res_2841_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
size_t v_x_16255__boxed_2845_; uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_x_16255__boxed_2845_ = lean_unbox_usize(v_x_2843_);
lean_dec(v_x_2843_);
v_res_2846_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2842_, v_x_16255__boxed_2845_, v_x_2844_);
lean_dec_ref(v_x_2844_);
lean_dec_ref(v_x_2842_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2848_, lean_object* v_x_2849_){
_start:
{
uint64_t v___x_2850_; size_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = l_Lean_instHashableExtraModUse_hash(v_x_2849_);
v___x_2851_ = lean_uint64_to_usize(v___x_2850_);
v___x_2852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2848_, v___x_2851_, v_x_2849_);
return v___x_2852_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2848_ = stack[0].m_obj;
lean_object* v_x_2849_ = stack[1].m_obj;
uint8_t v_res_2853_;
v_res_2853_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2848_, v_x_2849_);
stack->m_num = v_res_2853_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2854_, lean_object* v_x_2855_){
_start:
{
uint8_t v_res_2856_; lean_object* v_r_2857_; 
v_res_2856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2854_, v_x_2855_);
lean_dec_ref(v_x_2855_);
lean_dec_ref(v_x_2854_);
v_r_2857_ = lean_box(v_res_2856_);
return v_r_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0(lean_object* v___x_2858_, lean_object* v_entry_2859_, lean_object* v_s_2860_){
_start:
{
lean_object* v_addEntryFn_2861_; lean_object* v_importedEntries_2862_; lean_object* v_state_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
v_addEntryFn_2861_ = lean_ctor_get(v___x_2858_, 3);
lean_inc(v_addEntryFn_2861_);
lean_dec_ref(v___x_2858_);
v_importedEntries_2862_ = lean_ctor_get(v_s_2860_, 0);
v_state_2863_ = lean_ctor_get(v_s_2860_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_s_2860_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2865_ = v_s_2860_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_state_2863_);
lean_inc(v_importedEntries_2862_);
lean_dec(v_s_2860_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v_state_2867_; lean_object* v___x_2869_; 
v_state_2867_ = lean_apply_2(v_addEntryFn_2861_, v_state_2863_, v_entry_2859_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_state_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_importedEntries_2862_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_state_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2872_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3));
v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2883_ = l_Lean_stringToMessageData(v___x_2882_);
return v___x_2883_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_cls_2887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2888_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9));
v___x_2889_ = l_Lean_Name_append(v___x_2888_, v_cls_2887_);
return v___x_2889_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2892_ = l_Lean_stringToMessageData(v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2895_ = l_Lean_stringToMessageData(v___x_2894_);
return v___x_2895_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2900_, uint8_t v_isMeta_2901_, lean_object* v_hint_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_env_2942_; uint8_t v_isExporting_2943_; lean_object* v_entry_2944_; lean_object* v___x_2945_; lean_object* v_env_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_2941_ = lean_st_ref_get(v___y_2906_);
v_env_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_ref(v_env_2942_);
lean_dec(v___x_2941_);
v_isExporting_2943_ = lean_ctor_get_uint8(v_env_2942_, sizeof(void*)*13);
lean_dec_ref(v_env_2942_);
lean_inc(v_mod_2900_);
v_entry_2944_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2944_, 0, v_mod_2900_);
lean_ctor_set_uint8(v_entry_2944_, sizeof(void*)*1, v_isExporting_2943_);
lean_ctor_set_uint8(v_entry_2944_, sizeof(void*)*1 + 1, v_isMeta_2901_);
v___x_2945_ = lean_st_ref_get(v___y_2906_);
v_env_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc_ref(v_env_2946_);
lean_dec(v___x_2945_);
v___x_2947_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2948_ = lean_box(1);
v___x_2949_ = lean_box(0);
v___x_2950_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2940_, v___x_2947_, v_env_2946_, v___x_2948_, v___x_2949_);
v___x_2951_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2950_, v_entry_2944_);
lean_dec(v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v_toCold_2952_; lean_object* v_options_2953_; lean_object* v_inheritedTraceOptions_2954_; uint8_t v_hasTrace_2955_; lean_object* v___f_2956_; uint8_t v___x_2957_; lean_object* v___y_2959_; lean_object* v___y_2960_; 
v_toCold_2952_ = lean_ctor_get(v___y_2905_, 0);
v_options_2953_ = lean_ctor_get(v_toCold_2952_, 2);
v_inheritedTraceOptions_2954_ = lean_ctor_get(v_toCold_2952_, 11);
v_hasTrace_2955_ = lean_ctor_get_uint8(v_options_2953_, sizeof(void*)*1);
v___f_2956_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2956_, 0, v___x_2947_);
lean_closure_set(v___f_2956_, 1, v_entry_2944_);
v___x_2957_ = 1;
if (v_hasTrace_2955_ == 0)
{
lean_dec(v_hint_2902_);
lean_dec(v_mod_2900_);
v___y_2959_ = v___y_2904_;
v___y_2960_ = v___y_2906_;
goto v___jp_2958_;
}
else
{
lean_object* v_cls_2987_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_cls_2987_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_3007_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_3008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2954_, v_options_2953_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec(v_hint_2902_);
lean_dec(v_mod_2900_);
v___y_2959_ = v___y_2904_;
v___y_2960_ = v___y_2906_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_3009_; lean_object* v___y_3011_; 
v___x_3009_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_2943_ == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3011_ = v___x_3018_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3011_ = v___x_3019_;
goto v___jp_3010_;
}
v___jp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_inc_ref(v___y_3011_);
v___x_3012_ = l_Lean_stringToMessageData(v___y_3011_);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3009_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
if (v_isMeta_2901_ == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_2994_ = v___x_3015_;
v___y_2995_ = v___x_3016_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3017_; 
v___x_3017_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_2994_ = v___x_3015_;
v___y_2995_ = v___x_3017_;
goto v___jp_2993_;
}
}
}
v___jp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___y_2989_);
lean_ctor_set(v___x_2991_, 1, v___y_2990_);
v___x_2992_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2987_, v___x_2991_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
v___y_2959_ = v___y_2904_;
v___y_2960_ = v___y_2906_;
goto v___jp_2958_;
}
else
{
lean_dec_ref(v___f_2956_);
return v___x_2992_;
}
}
v___jp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
lean_inc_ref(v___y_2995_);
v___x_2996_ = l_Lean_stringToMessageData(v___y_2995_);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___y_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Lean_MessageData_ofName(v_mod_2900_);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = l_Lean_Name_isAnonymous(v_hint_2902_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3004_ = l_Lean_MessageData_ofName(v_hint_2902_);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___y_2989_ = v___x_3001_;
v___y_2990_ = v___x_3005_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3006_; 
lean_dec(v_hint_2902_);
v___x_3006_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_2989_ = v___x_3001_;
v___y_2990_ = v___x_3006_;
goto v___jp_2988_;
}
}
}
v___jp_2958_:
{
lean_object* v___x_2961_; lean_object* v_toEnvExtension_2962_; uint8_t v_logWrites_2963_; 
v___x_2961_ = lean_st_ref_take(v___y_2960_);
v_toEnvExtension_2962_ = lean_ctor_get(v___x_2947_, 0);
v_logWrites_2963_ = lean_ctor_get_uint8(v_toEnvExtension_2962_, sizeof(void*)*6);
if (v_logWrites_2963_ == 0)
{
lean_object* v_env_2964_; lean_object* v_nextMacroScope_2965_; lean_object* v_ngen_2966_; lean_object* v_auxDeclNGen_2967_; lean_object* v_traceState_2968_; lean_object* v_recordedDeps_2969_; lean_object* v_messages_2970_; lean_object* v_infoState_2971_; lean_object* v_snapshotTasks_2972_; lean_object* v_asyncMode_2973_; lean_object* v___x_2974_; 
v_env_2964_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_ref(v_env_2964_);
v_nextMacroScope_2965_ = lean_ctor_get(v___x_2961_, 1);
lean_inc(v_nextMacroScope_2965_);
v_ngen_2966_ = lean_ctor_get(v___x_2961_, 2);
lean_inc_ref(v_ngen_2966_);
v_auxDeclNGen_2967_ = lean_ctor_get(v___x_2961_, 3);
lean_inc_ref(v_auxDeclNGen_2967_);
v_traceState_2968_ = lean_ctor_get(v___x_2961_, 4);
lean_inc_ref(v_traceState_2968_);
v_recordedDeps_2969_ = lean_ctor_get(v___x_2961_, 6);
lean_inc_ref(v_recordedDeps_2969_);
v_messages_2970_ = lean_ctor_get(v___x_2961_, 7);
lean_inc_ref(v_messages_2970_);
v_infoState_2971_ = lean_ctor_get(v___x_2961_, 8);
lean_inc_ref(v_infoState_2971_);
v_snapshotTasks_2972_ = lean_ctor_get(v___x_2961_, 9);
lean_inc_ref(v_snapshotTasks_2972_);
lean_dec(v___x_2961_);
v_asyncMode_2973_ = lean_ctor_get(v_toEnvExtension_2962_, 2);
lean_inc_ref(v_toEnvExtension_2962_);
v___x_2974_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2962_, v_env_2964_, v___f_2956_, v_asyncMode_2973_, v___x_2949_, v___x_2957_);
v___y_2909_ = v_ngen_2966_;
v___y_2910_ = v_auxDeclNGen_2967_;
v___y_2911_ = v___y_2960_;
v___y_2912_ = v_recordedDeps_2969_;
v___y_2913_ = v_nextMacroScope_2965_;
v___y_2914_ = v_snapshotTasks_2972_;
v___y_2915_ = v___y_2959_;
v___y_2916_ = v_traceState_2968_;
v___y_2917_ = v_infoState_2971_;
v___y_2918_ = v_messages_2970_;
v___y_2919_ = v___x_2974_;
goto v___jp_2908_;
}
else
{
lean_object* v_env_2975_; lean_object* v_nextMacroScope_2976_; lean_object* v_ngen_2977_; lean_object* v_auxDeclNGen_2978_; lean_object* v_traceState_2979_; lean_object* v_recordedDeps_2980_; lean_object* v_messages_2981_; lean_object* v_infoState_2982_; lean_object* v_snapshotTasks_2983_; lean_object* v_asyncMode_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_env_2975_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_ref(v_env_2975_);
v_nextMacroScope_2976_ = lean_ctor_get(v___x_2961_, 1);
lean_inc(v_nextMacroScope_2976_);
v_ngen_2977_ = lean_ctor_get(v___x_2961_, 2);
lean_inc_ref(v_ngen_2977_);
v_auxDeclNGen_2978_ = lean_ctor_get(v___x_2961_, 3);
lean_inc_ref(v_auxDeclNGen_2978_);
v_traceState_2979_ = lean_ctor_get(v___x_2961_, 4);
lean_inc_ref(v_traceState_2979_);
v_recordedDeps_2980_ = lean_ctor_get(v___x_2961_, 6);
lean_inc_ref(v_recordedDeps_2980_);
v_messages_2981_ = lean_ctor_get(v___x_2961_, 7);
lean_inc_ref(v_messages_2981_);
v_infoState_2982_ = lean_ctor_get(v___x_2961_, 8);
lean_inc_ref(v_infoState_2982_);
v_snapshotTasks_2983_ = lean_ctor_get(v___x_2961_, 9);
lean_inc_ref(v_snapshotTasks_2983_);
lean_dec(v___x_2961_);
v_asyncMode_2984_ = lean_ctor_get(v_toEnvExtension_2962_, 2);
lean_inc_ref_n(v_toEnvExtension_2962_, 2);
v___x_2985_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2962_, v_env_2975_);
lean_dec_ref(v_env_2975_);
v___x_2986_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2962_, v___x_2985_, v___f_2956_, v_asyncMode_2984_, v___x_2949_, v___x_2957_);
v___y_2909_ = v_ngen_2977_;
v___y_2910_ = v_auxDeclNGen_2978_;
v___y_2911_ = v___y_2960_;
v___y_2912_ = v_recordedDeps_2980_;
v___y_2913_ = v_nextMacroScope_2976_;
v___y_2914_ = v_snapshotTasks_2983_;
v___y_2915_ = v___y_2959_;
v___y_2916_ = v_traceState_2979_;
v___y_2917_ = v_infoState_2982_;
v___y_2918_ = v_messages_2981_;
v___y_2919_ = v___x_2986_;
goto v___jp_2908_;
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec_ref_known(v_entry_2944_, 1);
lean_dec(v_hint_2902_);
lean_dec(v_mod_2900_);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
v___jp_2908_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v_mctx_2924_; lean_object* v_zetaDeltaFVarIds_2925_; lean_object* v_postponed_2926_; lean_object* v_diag_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2938_; 
v___x_2920_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_2921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2921_, 0, v___y_2919_);
lean_ctor_set(v___x_2921_, 1, v___y_2913_);
lean_ctor_set(v___x_2921_, 2, v___y_2909_);
lean_ctor_set(v___x_2921_, 3, v___y_2910_);
lean_ctor_set(v___x_2921_, 4, v___y_2916_);
lean_ctor_set(v___x_2921_, 5, v___x_2920_);
lean_ctor_set(v___x_2921_, 6, v___y_2912_);
lean_ctor_set(v___x_2921_, 7, v___y_2918_);
lean_ctor_set(v___x_2921_, 8, v___y_2917_);
lean_ctor_set(v___x_2921_, 9, v___y_2914_);
v___x_2922_ = lean_st_ref_put(v___y_2911_, v___x_2921_);
v___x_2923_ = lean_st_ref_take(v___y_2915_);
v_mctx_2924_ = lean_ctor_get(v___x_2923_, 0);
v_zetaDeltaFVarIds_2925_ = lean_ctor_get(v___x_2923_, 2);
v_postponed_2926_ = lean_ctor_get(v___x_2923_, 3);
v_diag_2927_ = lean_ctor_get(v___x_2923_, 4);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v___x_2923_, 1);
lean_dec(v_unused_2939_);
v___x_2929_ = v___x_2923_;
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_diag_2927_);
lean_inc(v_postponed_2926_);
lean_inc(v_zetaDeltaFVarIds_2925_);
lean_inc(v_mctx_2924_);
lean_dec(v___x_2923_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_mctx_2924_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_zetaDeltaFVarIds_2925_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_postponed_2926_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_diag_2927_);
v___x_2934_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_st_ref_put(v___y_2915_, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2931_);
return v___x_2936_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2900_ = stack[0].m_obj;
uint8_t v_isMeta_2901_ = stack[1].m_num;
lean_object* v_hint_2902_ = stack[2].m_obj;
lean_object* v___y_2903_ = stack[3].m_obj;
lean_object* v___y_2904_ = stack[4].m_obj;
lean_object* v___y_2905_ = stack[5].m_obj;
lean_object* v___y_2906_ = stack[6].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2900_, v_isMeta_2901_, v_hint_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_3023_, lean_object* v_isMeta_3024_, lean_object* v_hint_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
uint8_t v_isMeta_boxed_3031_; lean_object* v_res_3032_; 
v_isMeta_boxed_3031_ = lean_unbox(v_isMeta_3024_);
v_res_3032_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_3023_, v_isMeta_boxed_3031_, v_hint_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_3033_, lean_object* v_x_3034_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_box(0);
return v___x_3035_;
}
else
{
lean_object* v_key_3036_; lean_object* v_value_3037_; lean_object* v_tail_3038_; uint8_t v___x_3039_; 
v_key_3036_ = lean_ctor_get(v_x_3034_, 0);
v_value_3037_ = lean_ctor_get(v_x_3034_, 1);
v_tail_3038_ = lean_ctor_get(v_x_3034_, 2);
v___x_3039_ = lean_name_eq(v_key_3036_, v_a_3033_);
if (v___x_3039_ == 0)
{
v_x_3034_ = v_tail_3038_;
goto _start;
}
else
{
lean_object* v___x_3041_; 
lean_inc(v_value_3037_);
v___x_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_value_3037_);
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3042_, v_x_3043_);
lean_dec(v_x_3043_);
lean_dec(v_a_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v_buckets_3047_; lean_object* v___x_3048_; uint64_t v___y_3050_; 
v_buckets_3047_ = lean_ctor_get(v_m_3045_, 1);
v___x_3048_ = lean_array_get_size(v_buckets_3047_);
if (lean_obj_tag(v_a_3046_) == 0)
{
uint64_t v___x_3064_; 
v___x_3064_ = 1723ULL;
v___y_3050_ = v___x_3064_;
goto v___jp_3049_;
}
else
{
uint64_t v_hash_3065_; 
v_hash_3065_ = lean_ctor_get_uint64(v_a_3046_, sizeof(void*)*2);
v___y_3050_ = v_hash_3065_;
goto v___jp_3049_;
}
v___jp_3049_:
{
uint64_t v___x_3051_; uint64_t v___x_3052_; uint64_t v_fold_3053_; uint64_t v___x_3054_; uint64_t v___x_3055_; uint64_t v___x_3056_; size_t v___x_3057_; size_t v___x_3058_; size_t v___x_3059_; size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3051_ = 32ULL;
v___x_3052_ = lean_uint64_shift_right(v___y_3050_, v___x_3051_);
v_fold_3053_ = lean_uint64_xor(v___y_3050_, v___x_3052_);
v___x_3054_ = 16ULL;
v___x_3055_ = lean_uint64_shift_right(v_fold_3053_, v___x_3054_);
v___x_3056_ = lean_uint64_xor(v_fold_3053_, v___x_3055_);
v___x_3057_ = lean_uint64_to_usize(v___x_3056_);
v___x_3058_ = lean_usize_of_nat(v___x_3048_);
v___x_3059_ = ((size_t)1ULL);
v___x_3060_ = lean_usize_sub(v___x_3058_, v___x_3059_);
v___x_3061_ = lean_usize_land(v___x_3057_, v___x_3060_);
v___x_3062_ = lean_array_uget_borrowed(v_buckets_3047_, v___x_3061_);
v___x_3063_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3046_, v___x_3062_);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_m_3066_);
return v_res_3068_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_3069_, lean_object* v_declName_3070_, lean_object* v_as_3071_, size_t v_sz_3072_, size_t v_i_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_usize_dec_lt(v_i_3073_, v_sz_3072_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec(v_declName_3070_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_b_3074_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v_modules_3083_; lean_object* v___x_3084_; lean_object* v_a_3085_; lean_object* v___x_3086_; lean_object* v_toImport_3087_; lean_object* v_module_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3082_ = l_Lean_Environment_header(v___x_3069_);
v_modules_3083_ = lean_ctor_get(v___x_3082_, 3);
lean_inc_ref(v_modules_3083_);
lean_dec_ref(v___x_3082_);
v___x_3084_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3085_ = lean_array_uget_borrowed(v_as_3071_, v_i_3073_);
v___x_3086_ = lean_array_get(v___x_3084_, v_modules_3083_, v_a_3085_);
lean_dec_ref(v_modules_3083_);
v_toImport_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_toImport_3087_);
lean_dec(v___x_3086_);
v_module_3088_ = lean_ctor_get(v_toImport_3087_, 0);
lean_inc(v_module_3088_);
lean_dec_ref(v_toImport_3087_);
v___x_3089_ = lean_box(0);
v___x_3090_ = 0;
lean_inc(v_declName_3070_);
v___x_3091_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3088_, v___x_3090_, v_declName_3070_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3091_) == 0)
{
size_t v___x_3092_; size_t v___x_3093_; 
lean_dec_ref_known(v___x_3091_, 1);
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_add(v_i_3073_, v___x_3092_);
v_i_3073_ = v___x_3093_;
v_b_3074_ = v___x_3089_;
goto _start;
}
else
{
lean_dec(v_declName_3070_);
return v___x_3091_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3069_ = stack[0].m_obj;
lean_object* v_declName_3070_ = stack[1].m_obj;
lean_object* v_as_3071_ = stack[2].m_obj;
size_t v_sz_3072_ = stack[3].m_num;
size_t v_i_3073_ = stack[4].m_num;
lean_object* v_b_3074_ = stack[5].m_obj;
lean_object* v___y_3075_ = stack[6].m_obj;
lean_object* v___y_3076_ = stack[7].m_obj;
lean_object* v___y_3077_ = stack[8].m_obj;
lean_object* v___y_3078_ = stack[9].m_obj;
lean_object* v_res_3095_;
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3069_, v_declName_3070_, v_as_3071_, v_sz_3072_, v_i_3073_, v_b_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
stack->m_obj
 = v_res_3095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3096_, lean_object* v_declName_3097_, lean_object* v_as_3098_, lean_object* v_sz_3099_, lean_object* v_i_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
size_t v_sz_boxed_3107_; size_t v_i_boxed_3108_; lean_object* v_res_3109_; 
v_sz_boxed_3107_ = lean_unbox_usize(v_sz_3099_);
lean_dec(v_sz_3099_);
v_i_boxed_3108_ = lean_unbox_usize(v_i_3100_);
lean_dec(v_i_3100_);
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3096_, v_declName_3097_, v_as_3098_, v_sz_boxed_3107_, v_i_boxed_3108_, v_b_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec_ref(v_as_3098_);
lean_dec_ref(v___x_3096_);
return v_res_3109_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3110_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3113_, uint8_t v_isMeta_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_env_3125_; lean_object* v___y_3127_; lean_object* v___x_3140_; 
v___x_3120_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3121_ = lean_st_ref_get(v___y_3118_);
v_env_3125_ = lean_ctor_get(v___x_3121_, 0);
lean_inc_ref(v_env_3125_);
lean_dec(v___x_3121_);
v___x_3140_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3125_, v_declName_3113_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_dec_ref(v_env_3125_);
lean_dec(v_declName_3113_);
goto v___jp_3122_;
}
else
{
lean_object* v_val_3141_; lean_object* v___x_3142_; lean_object* v_modules_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_val_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_val_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = l_Lean_Environment_header(v_env_3125_);
v_modules_3143_ = lean_ctor_get(v___x_3142_, 3);
lean_inc_ref(v_modules_3143_);
lean_dec_ref(v___x_3142_);
v___x_3144_ = lean_array_get_size(v_modules_3143_);
v___x_3145_ = lean_nat_dec_lt(v_val_3141_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_dec_ref(v_modules_3143_);
lean_dec(v_val_3141_);
lean_dec_ref(v_env_3125_);
lean_dec(v_declName_3113_);
goto v___jp_3122_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___y_3149_; 
v___x_3146_ = lean_array_fget(v_modules_3143_, v_val_3141_);
lean_dec(v_val_3141_);
lean_dec_ref(v_modules_3143_);
v___x_3147_ = lean_st_ref_get(v___y_3118_);
if (v_isMeta_3114_ == 0)
{
lean_dec(v___x_3147_);
v___y_3149_ = v_isMeta_3114_;
goto v___jp_3148_;
}
else
{
lean_object* v_env_3160_; uint8_t v___x_3161_; 
v_env_3160_ = lean_ctor_get(v___x_3147_, 0);
lean_inc_ref(v_env_3160_);
lean_dec(v___x_3147_);
lean_inc(v_declName_3113_);
v___x_3161_ = l_Lean_isMarkedMeta(v_env_3160_, v_declName_3113_);
if (v___x_3161_ == 0)
{
v___y_3149_ = v_isMeta_3114_;
goto v___jp_3148_;
}
else
{
uint8_t v___x_3162_; 
v___x_3162_ = 0;
v___y_3149_ = v___x_3162_;
goto v___jp_3148_;
}
}
v___jp_3148_:
{
lean_object* v_toImport_3150_; lean_object* v_module_3151_; lean_object* v___x_3152_; 
v_toImport_3150_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_toImport_3150_);
lean_dec(v___x_3146_);
v_module_3151_ = lean_ctor_get(v_toImport_3150_, 0);
lean_inc(v_module_3151_);
lean_dec_ref(v_toImport_3150_);
lean_inc(v_declName_3113_);
v___x_3152_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3151_, v___y_3149_, v_declName_3113_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref_known(v___x_3152_, 1);
v___x_3153_ = l_Lean_indirectModUseExt;
v___x_3154_ = lean_box(1);
v___x_3155_ = lean_box(0);
lean_inc_ref(v_env_3125_);
v___x_3156_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3120_, v___x_3153_, v_env_3125_, v___x_3154_, v___x_3155_);
v___x_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3156_, v_declName_3113_);
lean_dec(v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3127_ = v___x_3158_;
goto v___jp_3126_;
}
else
{
lean_object* v_val_3159_; 
v_val_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v___x_3157_, 1);
v___y_3127_ = v_val_3159_;
goto v___jp_3126_;
}
}
else
{
lean_dec_ref(v_env_3125_);
lean_dec(v_declName_3113_);
return v___x_3152_;
}
}
}
}
v___jp_3122_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = lean_box(0);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
v___jp_3126_:
{
lean_object* v___x_3128_; size_t v_sz_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3128_ = lean_box(0);
v_sz_3129_ = lean_array_size(v___y_3127_);
v___x_3130_ = ((size_t)0ULL);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3125_, v_declName_3113_, v___y_3127_, v_sz_3129_, v___x_3130_, v___x_3128_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v_env_3125_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3139_);
v___x_3133_ = v___x_3131_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v___x_3131_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3128_);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3128_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
return v___x_3131_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3113_ = stack[0].m_obj;
uint8_t v_isMeta_3114_ = stack[1].m_num;
lean_object* v___y_3115_ = stack[2].m_obj;
lean_object* v___y_3116_ = stack[3].m_obj;
lean_object* v___y_3117_ = stack[4].m_obj;
lean_object* v___y_3118_ = stack[5].m_obj;
lean_object* v_res_3163_;
v_res_3163_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3113_, v_isMeta_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
stack->m_obj
 = v_res_3163_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3164_, lean_object* v_isMeta_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_isMeta_boxed_3171_; lean_object* v_res_3172_; 
v_isMeta_boxed_3171_ = lean_unbox(v_isMeta_3165_);
v_res_3172_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3164_, v_isMeta_boxed_3171_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3172_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3173_, uint8_t v_isExporting_3174_, lean_object* v___x_3175_, lean_object* v___y_3176_, lean_object* v___x_3177_, lean_object* v_a_x3f_3178_){
_start:
{
lean_object* v___x_3180_; lean_object* v_env_3181_; lean_object* v_nextMacroScope_3182_; lean_object* v_ngen_3183_; lean_object* v_auxDeclNGen_3184_; lean_object* v_traceState_3185_; lean_object* v_recordedDeps_3186_; lean_object* v_messages_3187_; lean_object* v_infoState_3188_; lean_object* v_snapshotTasks_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3214_; 
v___x_3180_ = lean_st_ref_take(v___y_3173_);
v_env_3181_ = lean_ctor_get(v___x_3180_, 0);
v_nextMacroScope_3182_ = lean_ctor_get(v___x_3180_, 1);
v_ngen_3183_ = lean_ctor_get(v___x_3180_, 2);
v_auxDeclNGen_3184_ = lean_ctor_get(v___x_3180_, 3);
v_traceState_3185_ = lean_ctor_get(v___x_3180_, 4);
v_recordedDeps_3186_ = lean_ctor_get(v___x_3180_, 6);
v_messages_3187_ = lean_ctor_get(v___x_3180_, 7);
v_infoState_3188_ = lean_ctor_get(v___x_3180_, 8);
v_snapshotTasks_3189_ = lean_ctor_get(v___x_3180_, 9);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3180_, 5);
lean_dec(v_unused_3215_);
v___x_3191_ = v___x_3180_;
v_isShared_3192_ = v_isSharedCheck_3214_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_snapshotTasks_3189_);
lean_inc(v_infoState_3188_);
lean_inc(v_messages_3187_);
lean_inc(v_recordedDeps_3186_);
lean_inc(v_traceState_3185_);
lean_inc(v_auxDeclNGen_3184_);
lean_inc(v_ngen_3183_);
lean_inc(v_nextMacroScope_3182_);
lean_inc(v_env_3181_);
lean_dec(v___x_3180_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3214_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = l_Lean_Environment_setExporting(v_env_3181_, v_isExporting_3174_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 5, v___x_3175_);
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_nextMacroScope_3182_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_ngen_3183_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_auxDeclNGen_3184_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v_traceState_3185_);
lean_ctor_set(v_reuseFailAlloc_3213_, 5, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3213_, 6, v_recordedDeps_3186_);
lean_ctor_set(v_reuseFailAlloc_3213_, 7, v_messages_3187_);
lean_ctor_set(v_reuseFailAlloc_3213_, 8, v_infoState_3188_);
lean_ctor_set(v_reuseFailAlloc_3213_, 9, v_snapshotTasks_3189_);
v___x_3195_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_mctx_3198_; lean_object* v_zetaDeltaFVarIds_3199_; lean_object* v_postponed_3200_; lean_object* v_diag_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3211_; 
v___x_3196_ = lean_st_ref_put(v___y_3173_, v___x_3195_);
v___x_3197_ = lean_st_ref_take(v___y_3176_);
v_mctx_3198_ = lean_ctor_get(v___x_3197_, 0);
v_zetaDeltaFVarIds_3199_ = lean_ctor_get(v___x_3197_, 2);
v_postponed_3200_ = lean_ctor_get(v___x_3197_, 3);
v_diag_3201_ = lean_ctor_get(v___x_3197_, 4);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v___x_3197_, 1);
lean_dec(v_unused_3212_);
v___x_3203_ = v___x_3197_;
v_isShared_3204_ = v_isSharedCheck_3211_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_diag_3201_);
lean_inc(v_postponed_3200_);
lean_inc(v_zetaDeltaFVarIds_3199_);
lean_inc(v_mctx_3198_);
lean_dec(v___x_3197_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3211_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = lean_box(0);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 1, v___x_3177_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_mctx_3198_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_zetaDeltaFVarIds_3199_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v_postponed_3200_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v_diag_3201_);
v___x_3207_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_st_ref_put(v___y_3176_, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3205_);
return v___x_3209_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3173_ = stack[0].m_obj;
uint8_t v_isExporting_3174_ = stack[1].m_num;
lean_object* v___x_3175_ = stack[2].m_obj;
lean_object* v___y_3176_ = stack[3].m_obj;
lean_object* v___x_3177_ = stack[4].m_obj;
lean_object* v_a_x3f_3178_ = stack[5].m_obj;
lean_object* v_res_3216_;
v_res_3216_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3173_, v_isExporting_3174_, v___x_3175_, v___y_3176_, v___x_3177_, v_a_x3f_3178_);
stack->m_obj
 = v_res_3216_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3217_, lean_object* v_isExporting_3218_, lean_object* v___x_3219_, lean_object* v___y_3220_, lean_object* v___x_3221_, lean_object* v_a_x3f_3222_, lean_object* v___y_3223_){
_start:
{
uint8_t v_isExporting_boxed_3224_; lean_object* v_res_3225_; 
v_isExporting_boxed_3224_ = lean_unbox(v_isExporting_3218_);
v_res_3225_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3217_, v_isExporting_boxed_3224_, v___x_3219_, v___y_3220_, v___x_3221_, v_a_x3f_3222_);
lean_dec(v_a_x3f_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3217_);
return v_res_3225_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3226_, uint8_t v_isExporting_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v___x_3233_; lean_object* v_env_3234_; lean_object* v___x_3235_; uint8_t v_isModule_3236_; 
v___x_3233_ = lean_st_ref_get(v___y_3231_);
v_env_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc_ref(v_env_3234_);
lean_dec(v___x_3233_);
v___x_3235_ = l_Lean_Environment_header(v_env_3234_);
v_isModule_3236_ = lean_ctor_get_uint8(v___x_3235_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3235_);
if (v_isModule_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_dec_ref(v_env_3234_);
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
lean_inc(v___y_3229_);
lean_inc_ref(v___y_3228_);
v___x_3237_ = lean_apply_5(v_x_3226_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, lean_box(0));
return v___x_3237_;
}
else
{
uint8_t v_isExporting_3238_; 
v_isExporting_3238_ = lean_ctor_get_uint8(v_env_3234_, sizeof(void*)*13);
lean_dec_ref(v_env_3234_);
if (v_isExporting_3227_ == 0)
{
if (v_isExporting_3238_ == 0)
{
lean_object* v___x_3305_; 
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
lean_inc(v___y_3229_);
lean_inc_ref(v___y_3228_);
v___x_3305_ = lean_apply_5(v_x_3226_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, lean_box(0));
return v___x_3305_;
}
else
{
goto v___jp_3239_;
}
}
else
{
if (v_isExporting_3238_ == 0)
{
goto v___jp_3239_;
}
else
{
lean_object* v___x_3306_; 
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
lean_inc(v___y_3229_);
lean_inc_ref(v___y_3228_);
v___x_3306_ = lean_apply_5(v_x_3226_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, lean_box(0));
return v___x_3306_;
}
}
v___jp_3239_:
{
lean_object* v___x_3240_; lean_object* v_env_3241_; lean_object* v_nextMacroScope_3242_; lean_object* v_ngen_3243_; lean_object* v_auxDeclNGen_3244_; lean_object* v_traceState_3245_; lean_object* v_recordedDeps_3246_; lean_object* v_messages_3247_; lean_object* v_infoState_3248_; lean_object* v_snapshotTasks_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3303_; 
v___x_3240_ = lean_st_ref_take(v___y_3231_);
v_env_3241_ = lean_ctor_get(v___x_3240_, 0);
v_nextMacroScope_3242_ = lean_ctor_get(v___x_3240_, 1);
v_ngen_3243_ = lean_ctor_get(v___x_3240_, 2);
v_auxDeclNGen_3244_ = lean_ctor_get(v___x_3240_, 3);
v_traceState_3245_ = lean_ctor_get(v___x_3240_, 4);
v_recordedDeps_3246_ = lean_ctor_get(v___x_3240_, 6);
v_messages_3247_ = lean_ctor_get(v___x_3240_, 7);
v_infoState_3248_ = lean_ctor_get(v___x_3240_, 8);
v_snapshotTasks_3249_ = lean_ctor_get(v___x_3240_, 9);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v___x_3240_, 5);
lean_dec(v_unused_3304_);
v___x_3251_ = v___x_3240_;
v_isShared_3252_ = v_isSharedCheck_3303_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_snapshotTasks_3249_);
lean_inc(v_infoState_3248_);
lean_inc(v_messages_3247_);
lean_inc(v_recordedDeps_3246_);
lean_inc(v_traceState_3245_);
lean_inc(v_auxDeclNGen_3244_);
lean_inc(v_ngen_3243_);
lean_inc(v_nextMacroScope_3242_);
lean_inc(v_env_3241_);
lean_dec(v___x_3240_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3303_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3253_ = l_Lean_Environment_setExporting(v_env_3241_, v_isExporting_3227_);
v___x_3254_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 5, v___x_3254_);
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3256_ = v___x_3251_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_nextMacroScope_3242_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_ngen_3243_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_auxDeclNGen_3244_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_traceState_3245_);
lean_ctor_set(v_reuseFailAlloc_3302_, 5, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3302_, 6, v_recordedDeps_3246_);
lean_ctor_set(v_reuseFailAlloc_3302_, 7, v_messages_3247_);
lean_ctor_set(v_reuseFailAlloc_3302_, 8, v_infoState_3248_);
lean_ctor_set(v_reuseFailAlloc_3302_, 9, v_snapshotTasks_3249_);
v___x_3256_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_mctx_3259_; lean_object* v_zetaDeltaFVarIds_3260_; lean_object* v_postponed_3261_; lean_object* v_diag_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3300_; 
v___x_3257_ = lean_st_ref_put(v___y_3231_, v___x_3256_);
v___x_3258_ = lean_st_ref_take(v___y_3229_);
v_mctx_3259_ = lean_ctor_get(v___x_3258_, 0);
v_zetaDeltaFVarIds_3260_ = lean_ctor_get(v___x_3258_, 2);
v_postponed_3261_ = lean_ctor_get(v___x_3258_, 3);
v_diag_3262_ = lean_ctor_get(v___x_3258_, 4);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v___x_3258_, 1);
lean_dec(v_unused_3301_);
v___x_3264_ = v___x_3258_;
v_isShared_3265_ = v_isSharedCheck_3300_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_diag_3262_);
lean_inc(v_postponed_3261_);
lean_inc(v_zetaDeltaFVarIds_3260_);
lean_inc(v_mctx_3259_);
lean_dec(v___x_3258_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3300_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 1, v___x_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_mctx_3259_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v_zetaDeltaFVarIds_3260_);
lean_ctor_set(v_reuseFailAlloc_3299_, 3, v_postponed_3261_);
lean_ctor_set(v_reuseFailAlloc_3299_, 4, v_diag_3262_);
v___x_3268_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v_r_3270_; 
v___x_3269_ = lean_st_ref_put(v___y_3229_, v___x_3268_);
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
lean_inc(v___y_3229_);
lean_inc_ref(v___y_3228_);
v_r_3270_ = lean_apply_5(v_x_3226_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, lean_box(0));
if (lean_obj_tag(v_r_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3287_; 
v_a_3271_ = lean_ctor_get(v_r_3270_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_r_3270_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3273_ = v_r_3270_;
v_isShared_3274_ = v_isSharedCheck_3287_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v_r_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3287_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
lean_inc(v_a_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 1);
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v___x_3277_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3231_, v_isExporting_3238_, v___x_3254_, v___y_3229_, v___x_3266_, v___x_3276_);
lean_dec_ref(v___x_3276_);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; 
v_unused_3285_ = lean_ctor_get(v___x_3277_, 0);
lean_dec(v_unused_3285_);
v___x_3279_ = v___x_3277_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_dec(v___x_3277_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v_a_3271_);
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3271_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3288_ = lean_ctor_get(v_r_3270_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v_r_3270_, 1);
v___x_3289_ = lean_box(0);
v___x_3290_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3231_, v_isExporting_3238_, v___x_3254_, v___y_3229_, v___x_3266_, v___x_3289_);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3298_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 1);
lean_ctor_set(v___x_3292_, 0, v_a_3288_);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3288_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3226_ = stack[0].m_obj;
uint8_t v_isExporting_3227_ = stack[1].m_num;
lean_object* v___y_3228_ = stack[2].m_obj;
lean_object* v___y_3229_ = stack[3].m_obj;
lean_object* v___y_3230_ = stack[4].m_obj;
lean_object* v___y_3231_ = stack[5].m_obj;
lean_object* v_res_3307_;
v_res_3307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3226_, v_isExporting_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
stack->m_obj
 = v_res_3307_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3308_, lean_object* v_isExporting_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
uint8_t v_isExporting_boxed_3315_; lean_object* v_res_3316_; 
v_isExporting_boxed_3315_ = lean_unbox(v_isExporting_3309_);
v_res_3316_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3308_, v_isExporting_boxed_3315_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3316_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3317_, uint8_t v_when_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
if (v_when_3318_ == 0)
{
lean_object* v___x_3324_; 
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
v___x_3324_ = lean_apply_5(v_x_3317_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, lean_box(0));
return v___x_3324_;
}
else
{
uint8_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = 0;
v___x_3326_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3317_, v___x_3325_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3326_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3317_ = stack[0].m_obj;
uint8_t v_when_3318_ = stack[1].m_num;
lean_object* v___y_3319_ = stack[2].m_obj;
lean_object* v___y_3320_ = stack[3].m_obj;
lean_object* v___y_3321_ = stack[4].m_obj;
lean_object* v___y_3322_ = stack[5].m_obj;
lean_object* v_res_3327_;
v_res_3327_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3317_, v_when_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
stack->m_obj
 = v_res_3327_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3328_, lean_object* v_when_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v_when_boxed_3335_; lean_object* v_res_3336_; 
v_when_boxed_3335_ = lean_unbox(v_when_3329_);
v_res_3336_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3328_, v_when_boxed_3335_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
return v_res_3336_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_3337_, uint8_t v_showInfo_3338_, uint8_t v_minIndexable_3339_, lean_object* v_attrName_3340_, lean_object* v___x_3341_, lean_object* v_declName_3342_, lean_object* v_stx_3343_, uint8_t v_attrKind_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___f_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___y_3370_; lean_object* v___x_3380_; 
v___x_3348_ = 0;
v___x_3349_ = lean_box(v___x_3348_);
v___x_3350_ = lean_box(v_attrKind_3344_);
v___x_3351_ = lean_box(v_showInfo_3338_);
v___x_3352_ = lean_box(v_minIndexable_3339_);
lean_inc(v_declName_3342_);
v___f_3353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3353_, 0, v_declName_3342_);
lean_closure_set(v___f_3353_, 1, v___x_3349_);
lean_closure_set(v___f_3353_, 2, v___x_3350_);
lean_closure_set(v___f_3353_, 3, v_stx_3343_);
lean_closure_set(v___f_3353_, 4, v_ext_3337_);
lean_closure_set(v___f_3353_, 5, v___x_3351_);
lean_closure_set(v___f_3353_, 6, v___x_3352_);
lean_closure_set(v___f_3353_, 7, v_attrName_3340_);
v___x_3354_ = 1;
v___x_3355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3356_ = lean_unsigned_to_nat(32u);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_3356_);
lean_dec_ref(v___x_3357_);
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3362_ = lean_box(0);
lean_inc(v___x_3341_);
v___x_3363_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3363_, 0, v___x_3355_);
lean_ctor_set(v___x_3363_, 1, v___x_3341_);
lean_ctor_set(v___x_3363_, 2, v___x_3360_);
lean_ctor_set(v___x_3363_, 3, v___x_3361_);
lean_ctor_set(v___x_3363_, 4, v___x_3362_);
lean_ctor_set(v___x_3363_, 5, v___x_3358_);
lean_ctor_set(v___x_3363_, 6, v___x_3362_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7, v___x_3348_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 1, v___x_3348_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 2, v___x_3348_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 3, v___x_3354_);
v___x_3364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3364_);
lean_ctor_set(v___x_3367_, 1, v___x_3365_);
lean_ctor_set(v___x_3367_, 2, v___x_3341_);
lean_ctor_set(v___x_3367_, 3, v___x_3359_);
lean_ctor_set(v___x_3367_, 4, v___x_3366_);
v___x_3368_ = lean_st_mk_ref(v___x_3367_);
v___x_3380_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3342_, v___x_3348_, v___x_3363_, v___x_3368_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3380_, 1);
v___x_3381_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3353_, v___x_3354_, v___x_3363_, v___x_3368_, v___y_3345_, v___y_3346_);
lean_dec_ref_known(v___x_3363_, 7);
v___y_3370_ = v___x_3381_;
goto v___jp_3369_;
}
else
{
lean_dec_ref_known(v___x_3363_, 7);
lean_dec_ref(v___f_3353_);
v___y_3370_ = v___x_3380_;
goto v___jp_3369_;
}
v___jp_3369_:
{
if (lean_obj_tag(v___y_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
v_a_3371_ = lean_ctor_get(v___y_3370_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___y_3370_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3373_ = v___y_3370_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___y_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_st_ref_get(v___x_3368_);
lean_dec(v___x_3368_);
lean_dec(v___x_3375_);
if (v_isShared_3374_ == 0)
{
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3371_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
else
{
lean_dec(v___x_3368_);
return v___y_3370_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_3337_ = stack[0].m_obj;
uint8_t v_showInfo_3338_ = stack[1].m_num;
uint8_t v_minIndexable_3339_ = stack[2].m_num;
lean_object* v_attrName_3340_ = stack[3].m_obj;
lean_object* v___x_3341_ = stack[4].m_obj;
lean_object* v_declName_3342_ = stack[5].m_obj;
lean_object* v_stx_3343_ = stack[6].m_obj;
uint8_t v_attrKind_3344_ = stack[7].m_num;
lean_object* v___y_3345_ = stack[8].m_obj;
lean_object* v___y_3346_ = stack[9].m_obj;
lean_object* v_res_3382_;
v_res_3382_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_3337_, v_showInfo_3338_, v_minIndexable_3339_, v_attrName_3340_, v___x_3341_, v_declName_3342_, v_stx_3343_, v_attrKind_3344_, v___y_3345_, v___y_3346_);
stack->m_obj
 = v_res_3382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_3383_, lean_object* v_showInfo_3384_, lean_object* v_minIndexable_3385_, lean_object* v_attrName_3386_, lean_object* v___x_3387_, lean_object* v_declName_3388_, lean_object* v_stx_3389_, lean_object* v_attrKind_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_showInfo_boxed_3394_; uint8_t v_minIndexable_boxed_3395_; uint8_t v_attrKind_boxed_3396_; lean_object* v_res_3397_; 
v_showInfo_boxed_3394_ = lean_unbox(v_showInfo_3384_);
v_minIndexable_boxed_3395_ = lean_unbox(v_minIndexable_3385_);
v_attrKind_boxed_3396_ = lean_unbox(v_attrKind_3390_);
v_res_3397_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_3383_, v_showInfo_boxed_3394_, v_minIndexable_boxed_3395_, v_attrName_3386_, v___x_3387_, v_declName_3388_, v_stx_3389_, v_attrKind_boxed_3396_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3397_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3420_, uint8_t v_minIndexable_3421_, uint8_t v_showInfo_3422_, lean_object* v_ext_3423_, lean_object* v_ref_3424_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___f_3431_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3477_; 
v___x_3426_ = lean_box(1);
v___x_3427_ = lean_box(v_showInfo_3422_);
lean_inc_n(v_attrName_3420_, 2);
lean_inc_ref(v_ext_3423_);
v___f_3428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3428_, 0, v_ext_3423_);
lean_closure_set(v___f_3428_, 1, v___x_3426_);
lean_closure_set(v___f_3428_, 2, v___x_3427_);
lean_closure_set(v___f_3428_, 3, v_attrName_3420_);
v___x_3429_ = lean_box(v_showInfo_3422_);
v___x_3430_ = lean_box(v_minIndexable_3421_);
v___f_3431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3431_, 0, v_ext_3423_);
lean_closure_set(v___f_3431_, 1, v___x_3429_);
lean_closure_set(v___f_3431_, 2, v___x_3430_);
lean_closure_set(v___f_3431_, 3, v_attrName_3420_);
lean_closure_set(v___f_3431_, 4, v___x_3426_);
if (v_minIndexable_3421_ == 0)
{
if (v_showInfo_3422_ == 0)
{
lean_inc(v_attrName_3420_);
v___y_3477_ = v_attrName_3420_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3420_);
v___x_3506_ = lean_name_append_after(v_attrName_3420_, v___x_3505_);
v___y_3477_ = v___x_3506_;
goto v___jp_3476_;
}
}
else
{
if (v_showInfo_3422_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3420_);
v___x_3508_ = lean_name_append_after(v_attrName_3420_, v___x_3507_);
v___y_3477_ = v___x_3508_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3420_);
v___x_3510_ = lean_name_append_after(v_attrName_3420_, v___x_3509_);
v___y_3477_ = v___x_3510_;
goto v___jp_3476_;
}
}
v___jp_3432_:
{
lean_object* v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3436_ = 1;
v___x_3437_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3420_, v___x_3436_);
v___x_3438_ = lean_string_append(v___x_3435_, v___x_3437_);
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3440_ = lean_string_append(v___x_3438_, v___x_3439_);
v___x_3441_ = lean_string_append(v___x_3440_, v___x_3437_);
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3443_ = lean_string_append(v___x_3441_, v___x_3442_);
v___x_3444_ = lean_string_append(v___x_3443_, v___x_3437_);
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3446_ = lean_string_append(v___x_3444_, v___x_3445_);
v___x_3447_ = lean_string_append(v___x_3446_, v___x_3437_);
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3449_ = lean_string_append(v___x_3447_, v___x_3448_);
v___x_3450_ = lean_string_append(v___x_3449_, v___x_3437_);
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3452_ = lean_string_append(v___x_3450_, v___x_3451_);
v___x_3453_ = lean_string_append(v___x_3452_, v___x_3437_);
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
v___x_3456_ = lean_string_append(v___x_3455_, v___x_3437_);
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3458_ = lean_string_append(v___x_3456_, v___x_3457_);
v___x_3459_ = lean_string_append(v___x_3458_, v___x_3437_);
v___x_3460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3461_ = lean_string_append(v___x_3459_, v___x_3460_);
v___x_3462_ = lean_string_append(v___x_3461_, v___x_3437_);
v___x_3463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3464_ = lean_string_append(v___x_3462_, v___x_3463_);
v___x_3465_ = lean_string_append(v___x_3464_, v___x_3437_);
v___x_3466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
v___x_3468_ = lean_string_append(v___x_3467_, v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3470_ = lean_string_append(v___x_3468_, v___x_3469_);
v___x_3471_ = lean_string_append(v___y_3434_, v___x_3470_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = 1;
v___x_3473_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3473_, 0, v_ref_3424_);
lean_ctor_set(v___x_3473_, 1, v___y_3433_);
lean_ctor_set(v___x_3473_, 2, v___x_3471_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*3, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___f_3431_);
lean_ctor_set(v___x_3474_, 2, v___f_3428_);
v___x_3475_ = l_Lean_registerBuiltinAttribute(v___x_3474_);
return v___x_3475_;
}
v___jp_3476_:
{
if (v_minIndexable_3421_ == 0)
{
if (v_showInfo_3422_ == 0)
{
lean_object* v___x_3478_; uint8_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3479_ = 1;
lean_inc(v_attrName_3420_);
v___x_3480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3420_, v___x_3479_);
v___x_3481_ = lean_string_append(v___x_3478_, v___x_3480_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3483_ = lean_string_append(v___x_3481_, v___x_3482_);
v___y_3433_ = v___y_3477_;
v___y_3434_ = v___x_3483_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3420_);
v___x_3485_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3420_, v_showInfo_3422_);
v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
v___x_3487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3488_ = lean_string_append(v___x_3486_, v___x_3487_);
v___x_3489_ = lean_string_append(v___x_3488_, v___x_3485_);
lean_dec_ref(v___x_3485_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3491_ = lean_string_append(v___x_3489_, v___x_3490_);
v___y_3433_ = v___y_3477_;
v___y_3434_ = v___x_3491_;
goto v___jp_3432_;
}
}
else
{
if (v_showInfo_3422_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3420_);
v___x_3493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3420_, v_minIndexable_3421_);
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___y_3433_ = v___y_3477_;
v___y_3434_ = v___x_3496_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3420_);
v___x_3498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3420_, v_showInfo_3422_);
v___x_3499_ = lean_string_append(v___x_3497_, v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
v___x_3502_ = lean_string_append(v___x_3501_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
v___y_3433_ = v___y_3477_;
v___y_3434_ = v___x_3504_;
goto v___jp_3432_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_3420_ = stack[0].m_obj;
uint8_t v_minIndexable_3421_ = stack[1].m_num;
uint8_t v_showInfo_3422_ = stack[2].m_num;
lean_object* v_ext_3423_ = stack[3].m_obj;
lean_object* v_ref_3424_ = stack[4].m_obj;
lean_object* v_res_3511_;
v_res_3511_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3420_, v_minIndexable_3421_, v_showInfo_3422_, v_ext_3423_, v_ref_3424_);
stack->m_obj
 = v_res_3511_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3512_, lean_object* v_minIndexable_3513_, lean_object* v_showInfo_3514_, lean_object* v_ext_3515_, lean_object* v_ref_3516_, lean_object* v_a_3517_){
_start:
{
uint8_t v_minIndexable_boxed_3518_; uint8_t v_showInfo_boxed_3519_; lean_object* v_res_3520_; 
v_minIndexable_boxed_3518_ = lean_unbox(v_minIndexable_3513_);
v_showInfo_boxed_3519_ = lean_unbox(v_showInfo_3514_);
v_res_3520_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3512_, v_minIndexable_boxed_3518_, v_showInfo_boxed_3519_, v_ext_3515_, v_ref_3516_);
return v_res_3520_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3521_, lean_object* v_msg_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3522_ = stack[1].m_obj;
lean_object* v___y_3523_ = stack[2].m_obj;
lean_object* v___y_3524_ = stack[3].m_obj;
lean_object* v___y_3525_ = stack[4].m_obj;
lean_object* v___y_3526_ = stack[5].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_box(0), v_msg_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3530_, v_msg_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3537_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3538_, uint8_t v_attrKind_3539_, uint8_t v_showInfo_3540_, uint8_t v_minIndexable_3541_, lean_object* v_as_3542_, lean_object* v_as_x27_3543_, lean_object* v_b_3544_, lean_object* v_a_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3538_, v_attrKind_3539_, v_showInfo_3540_, v_minIndexable_3541_, v_as_x27_3543_, v_b_3544_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_3538_ = stack[0].m_obj;
uint8_t v_attrKind_3539_ = stack[1].m_num;
uint8_t v_showInfo_3540_ = stack[2].m_num;
uint8_t v_minIndexable_3541_ = stack[3].m_num;
lean_object* v_as_3542_ = stack[4].m_obj;
lean_object* v_as_x27_3543_ = stack[5].m_obj;
lean_object* v_b_3544_ = stack[6].m_obj;
lean_object* v___y_3546_ = stack[8].m_obj;
lean_object* v___y_3547_ = stack[9].m_obj;
lean_object* v___y_3548_ = stack[10].m_obj;
lean_object* v___y_3549_ = stack[11].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3538_, v_attrKind_3539_, v_showInfo_3540_, v_minIndexable_3541_, v_as_3542_, v_as_x27_3543_, v_b_3544_, lean_box(0), v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3553_, lean_object* v_attrKind_3554_, lean_object* v_showInfo_3555_, lean_object* v_minIndexable_3556_, lean_object* v_as_3557_, lean_object* v_as_x27_3558_, lean_object* v_b_3559_, lean_object* v_a_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v_attrKind_boxed_3566_; uint8_t v_showInfo_boxed_3567_; uint8_t v_minIndexable_boxed_3568_; lean_object* v_res_3569_; 
v_attrKind_boxed_3566_ = lean_unbox(v_attrKind_3554_);
v_showInfo_boxed_3567_ = lean_unbox(v_showInfo_3555_);
v_minIndexable_boxed_3568_ = lean_unbox(v_minIndexable_3556_);
v_res_3569_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3553_, v_attrKind_boxed_3566_, v_showInfo_boxed_3567_, v_minIndexable_boxed_3568_, v_as_3557_, v_as_x27_3558_, v_b_3559_, v_a_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_as_x27_3558_);
lean_dec(v_as_3557_);
return v_res_3569_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3570_, lean_object* v_x_3571_, uint8_t v_isExporting_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3571_, v_isExporting_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3571_ = stack[1].m_obj;
uint8_t v_isExporting_3572_ = stack[2].m_num;
lean_object* v___y_3573_ = stack[3].m_obj;
lean_object* v___y_3574_ = stack[4].m_obj;
lean_object* v___y_3575_ = stack[5].m_obj;
lean_object* v___y_3576_ = stack[6].m_obj;
lean_object* v_res_3579_;
v_res_3579_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_box(0), v_x_3571_, v_isExporting_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
stack->m_obj
 = v_res_3579_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_x_3581_, lean_object* v_isExporting_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
uint8_t v_isExporting_boxed_3588_; lean_object* v_res_3589_; 
v_isExporting_boxed_3588_ = lean_unbox(v_isExporting_3582_);
v_res_3589_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3580_, v_x_3581_, v_isExporting_boxed_3588_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3589_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3590_, lean_object* v_x_3591_, uint8_t v_when_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3591_, v_when_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3591_ = stack[1].m_obj;
uint8_t v_when_3592_ = stack[2].m_num;
lean_object* v___y_3593_ = stack[3].m_obj;
lean_object* v___y_3594_ = stack[4].m_obj;
lean_object* v___y_3595_ = stack[5].m_obj;
lean_object* v___y_3596_ = stack[6].m_obj;
lean_object* v_res_3599_;
v_res_3599_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_box(0), v_x_3591_, v_when_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
stack->m_obj
 = v_res_3599_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3600_, lean_object* v_x_3601_, lean_object* v_when_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
uint8_t v_when_boxed_3608_; lean_object* v_res_3609_; 
v_when_boxed_3608_ = lean_unbox(v_when_3602_);
v_res_3609_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3600_, v_x_3601_, v_when_boxed_3608_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3610_, lean_object* v_m_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3611_, v_a_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3614_, lean_object* v_m_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3614_, v_m_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_m_3615_);
return v_res_3617_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
uint8_t v___x_3621_; 
v___x_3621_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3619_, v_x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3619_ = stack[1].m_obj;
lean_object* v_x_3620_ = stack[2].m_obj;
uint8_t v_res_3622_;
v_res_3622_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_box(0), v_x_3619_, v_x_3620_);
stack->m_num = v_res_3622_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
uint8_t v_res_3626_; lean_object* v_r_3627_; 
v_res_3626_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3623_, v_x_3624_, v_x_3625_);
lean_dec_ref(v_x_3625_);
lean_dec_ref(v_x_3624_);
v_r_3627_ = lean_box(v_res_3626_);
return v_r_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3628_, lean_object* v_a_3629_, lean_object* v_x_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3629_, v_x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3632_, lean_object* v_a_3633_, lean_object* v_x_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3632_, v_a_3633_, v_x_3634_);
lean_dec(v_x_3634_);
lean_dec(v_a_3633_);
return v_res_3635_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3636_, lean_object* v_x_3637_, size_t v_x_3638_, lean_object* v_x_3639_){
_start:
{
uint8_t v___x_3640_; 
v___x_3640_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3637_, v_x_3638_, v_x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3637_ = stack[1].m_obj;
size_t v_x_3638_ = stack[2].m_num;
lean_object* v_x_3639_ = stack[3].m_obj;
uint8_t v_res_3641_;
v_res_3641_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_box(0), v_x_3637_, v_x_3638_, v_x_3639_);
stack->m_num = v_res_3641_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_){
_start:
{
size_t v_x_18090__boxed_3646_; uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_x_18090__boxed_3646_ = lean_unbox_usize(v_x_3644_);
lean_dec(v_x_3644_);
v_res_3647_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3642_, v_x_3643_, v_x_18090__boxed_3646_, v_x_3645_);
lean_dec_ref(v_x_3645_);
lean_dec_ref(v_x_3643_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3649_, lean_object* v_keys_3650_, lean_object* v_vals_3651_, lean_object* v_heq_3652_, lean_object* v_i_3653_, lean_object* v_k_3654_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3650_, v_i_3653_, v_k_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3650_ = stack[1].m_obj;
lean_object* v_vals_3651_ = stack[2].m_obj;
lean_object* v_i_3653_ = stack[4].m_obj;
lean_object* v_k_3654_ = stack[5].m_obj;
uint8_t v_res_3656_;
v_res_3656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_box(0), v_keys_3650_, v_vals_3651_, lean_box(0), v_i_3653_, v_k_3654_);
stack->m_num = v_res_3656_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3657_, lean_object* v_keys_3658_, lean_object* v_vals_3659_, lean_object* v_heq_3660_, lean_object* v_i_3661_, lean_object* v_k_3662_){
_start:
{
uint8_t v_res_3663_; lean_object* v_r_3664_; 
v_res_3663_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3657_, v_keys_3658_, v_vals_3659_, v_heq_3660_, v_i_3661_, v_k_3662_);
lean_dec_ref(v_k_3662_);
lean_dec_ref(v_vals_3659_);
lean_dec_ref(v_keys_3658_);
v_r_3664_ = lean_box(v_res_3663_);
return v_r_3664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_box(0);
v___x_3666_ = lean_unsigned_to_nat(16u);
v___x_3667_ = lean_mk_array(v___x_3666_, v___x_3665_);
return v___x_3667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3669_ = lean_unsigned_to_nat(0u);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___x_3668_);
return v___x_3670_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3673_ = lean_st_mk_ref(v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3675_;
v_res_3675_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3675_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3677_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3678_, lean_object* v_msg_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_ref_3683_; lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3730_; 
v_ref_3683_ = lean_ctor_get(v___y_3680_, 2);
v___x_3684_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3679_, v___y_3680_, v___y_3681_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3730_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3730_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v_traceState_3690_; lean_object* v_env_3691_; lean_object* v_nextMacroScope_3692_; lean_object* v_ngen_3693_; lean_object* v_auxDeclNGen_3694_; lean_object* v_cache_3695_; lean_object* v_recordedDeps_3696_; lean_object* v_messages_3697_; lean_object* v_infoState_3698_; lean_object* v_snapshotTasks_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3729_; 
v___x_3689_ = lean_st_ref_take(v___y_3681_);
v_traceState_3690_ = lean_ctor_get(v___x_3689_, 4);
v_env_3691_ = lean_ctor_get(v___x_3689_, 0);
v_nextMacroScope_3692_ = lean_ctor_get(v___x_3689_, 1);
v_ngen_3693_ = lean_ctor_get(v___x_3689_, 2);
v_auxDeclNGen_3694_ = lean_ctor_get(v___x_3689_, 3);
v_cache_3695_ = lean_ctor_get(v___x_3689_, 5);
v_recordedDeps_3696_ = lean_ctor_get(v___x_3689_, 6);
v_messages_3697_ = lean_ctor_get(v___x_3689_, 7);
v_infoState_3698_ = lean_ctor_get(v___x_3689_, 8);
v_snapshotTasks_3699_ = lean_ctor_get(v___x_3689_, 9);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3701_ = v___x_3689_;
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_snapshotTasks_3699_);
lean_inc(v_infoState_3698_);
lean_inc(v_messages_3697_);
lean_inc(v_recordedDeps_3696_);
lean_inc(v_cache_3695_);
lean_inc(v_traceState_3690_);
lean_inc(v_auxDeclNGen_3694_);
lean_inc(v_ngen_3693_);
lean_inc(v_nextMacroScope_3692_);
lean_inc(v_env_3691_);
lean_dec(v___x_3689_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint64_t v_tid_3703_; lean_object* v_traces_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3728_; 
v_tid_3703_ = lean_ctor_get_uint64(v_traceState_3690_, sizeof(void*)*1);
v_traces_3704_ = lean_ctor_get(v_traceState_3690_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_traceState_3690_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3706_ = v_traceState_3690_;
v_isShared_3707_ = v_isSharedCheck_3728_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_traces_3704_);
lean_dec(v_traceState_3690_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3728_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; double v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3708_ = lean_box(0);
v___x_3709_ = lean_box(0);
v___x_3710_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3711_ = 0;
v___x_3712_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3713_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3713_, 0, v_cls_3678_);
lean_ctor_set(v___x_3713_, 1, v___x_3709_);
lean_ctor_set(v___x_3713_, 2, v___x_3712_);
lean_ctor_set_float(v___x_3713_, sizeof(void*)*3, v___x_3710_);
lean_ctor_set_float(v___x_3713_, sizeof(void*)*3 + 8, v___x_3710_);
lean_ctor_set_uint8(v___x_3713_, sizeof(void*)*3 + 16, v___x_3711_);
v___x_3714_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3715_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v_a_3685_);
lean_ctor_set(v___x_3715_, 2, v___x_3714_);
lean_inc(v_ref_3683_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v_ref_3683_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_PersistentArray_push___redArg(v_traces_3704_, v___x_3716_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3717_);
v___x_3719_ = v___x_3706_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3717_);
lean_ctor_set_uint64(v_reuseFailAlloc_3727_, sizeof(void*)*1, v_tid_3703_);
v___x_3719_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v___x_3719_);
v___x_3721_ = v___x_3701_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_env_3691_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_nextMacroScope_3692_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_ngen_3693_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_auxDeclNGen_3694_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3726_, 5, v_cache_3695_);
lean_ctor_set(v_reuseFailAlloc_3726_, 6, v_recordedDeps_3696_);
lean_ctor_set(v_reuseFailAlloc_3726_, 7, v_messages_3697_);
lean_ctor_set(v_reuseFailAlloc_3726_, 8, v_infoState_3698_);
lean_ctor_set(v_reuseFailAlloc_3726_, 9, v_snapshotTasks_3699_);
v___x_3721_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3722_ = lean_st_ref_put(v___y_3681_, v___x_3721_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3708_);
v___x_3724_ = v___x_3687_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3708_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3678_ = stack[0].m_obj;
lean_object* v_msg_3679_ = stack[1].m_obj;
lean_object* v___y_3680_ = stack[2].m_obj;
lean_object* v___y_3681_ = stack[3].m_obj;
lean_object* v_res_3731_;
v_res_3731_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3678_, v_msg_3679_, v___y_3680_, v___y_3681_);
stack->m_obj
 = v_res_3731_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3732_, lean_object* v_msg_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3732_, v_msg_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3737_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3738_, uint8_t v_isMeta_3739_, lean_object* v_hint_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v_env_3762_; uint8_t v_isExporting_3763_; lean_object* v_entry_3764_; lean_object* v___x_3765_; lean_object* v_env_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3760_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_3761_ = lean_st_ref_get(v___y_3742_);
v_env_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc_ref(v_env_3762_);
lean_dec(v___x_3761_);
v_isExporting_3763_ = lean_ctor_get_uint8(v_env_3762_, sizeof(void*)*13);
lean_dec_ref(v_env_3762_);
lean_inc(v_mod_3738_);
v_entry_3764_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3764_, 0, v_mod_3738_);
lean_ctor_set_uint8(v_entry_3764_, sizeof(void*)*1, v_isExporting_3763_);
lean_ctor_set_uint8(v_entry_3764_, sizeof(void*)*1 + 1, v_isMeta_3739_);
v___x_3765_ = lean_st_ref_get(v___y_3742_);
v_env_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc_ref(v_env_3766_);
lean_dec(v___x_3765_);
v___x_3767_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3768_ = lean_box(1);
v___x_3769_ = lean_box(0);
v___x_3770_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3760_, v___x_3767_, v_env_3766_, v___x_3768_, v___x_3769_);
v___x_3771_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3770_, v_entry_3764_);
lean_dec(v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v_toCold_3772_; lean_object* v_options_3773_; lean_object* v_inheritedTraceOptions_3774_; uint8_t v_hasTrace_3775_; lean_object* v___f_3776_; uint8_t v___x_3777_; lean_object* v___y_3779_; 
v_toCold_3772_ = lean_ctor_get(v___y_3741_, 0);
v_options_3773_ = lean_ctor_get(v_toCold_3772_, 2);
v_inheritedTraceOptions_3774_ = lean_ctor_get(v_toCold_3772_, 11);
v_hasTrace_3775_ = lean_ctor_get_uint8(v_options_3773_, sizeof(void*)*1);
v___f_3776_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_3776_, 0, v___x_3767_);
lean_closure_set(v___f_3776_, 1, v_entry_3764_);
v___x_3777_ = 1;
if (v_hasTrace_3775_ == 0)
{
lean_dec(v_hint_3740_);
lean_dec(v_mod_3738_);
v___y_3779_ = v___y_3742_;
goto v___jp_3778_;
}
else
{
lean_object* v_cls_3797_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v_cls_3797_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_3817_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_3818_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3774_, v_options_3773_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_dec(v_hint_3740_);
lean_dec(v_mod_3738_);
v___y_3779_ = v___y_3742_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3819_; lean_object* v___y_3821_; 
v___x_3819_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_3763_ == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3821_ = v___x_3828_;
goto v___jp_3820_;
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3821_ = v___x_3829_;
goto v___jp_3820_;
}
v___jp_3820_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_inc_ref(v___y_3821_);
v___x_3822_ = l_Lean_stringToMessageData(v___y_3821_);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3819_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_3825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3823_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
if (v_isMeta_3739_ == 0)
{
lean_object* v___x_3826_; 
v___x_3826_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_3804_ = v___x_3825_;
v___y_3805_ = v___x_3826_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3827_; 
v___x_3827_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_3804_ = v___x_3825_;
v___y_3805_ = v___x_3827_;
goto v___jp_3803_;
}
}
}
v___jp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___y_3799_);
lean_ctor_set(v___x_3801_, 1, v___y_3800_);
v___x_3802_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3797_, v___x_3801_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_dec_ref_known(v___x_3802_, 1);
v___y_3779_ = v___y_3742_;
goto v___jp_3778_;
}
else
{
lean_dec_ref(v___f_3776_);
return v___x_3802_;
}
}
v___jp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
lean_inc_ref(v___y_3805_);
v___x_3806_ = l_Lean_stringToMessageData(v___y_3805_);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___y_3804_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = l_Lean_MessageData_ofName(v_mod_3738_);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_Name_isAnonymous(v_hint_3740_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3814_ = l_Lean_MessageData_ofName(v_hint_3740_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___y_3799_ = v___x_3811_;
v___y_3800_ = v___x_3815_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3816_; 
lean_dec(v_hint_3740_);
v___x_3816_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_3799_ = v___x_3811_;
v___y_3800_ = v___x_3816_;
goto v___jp_3798_;
}
}
}
v___jp_3778_:
{
lean_object* v___x_3780_; lean_object* v_toEnvExtension_3781_; lean_object* v_env_3782_; lean_object* v_nextMacroScope_3783_; lean_object* v_ngen_3784_; lean_object* v_auxDeclNGen_3785_; lean_object* v_traceState_3786_; lean_object* v_recordedDeps_3787_; lean_object* v_messages_3788_; lean_object* v_infoState_3789_; lean_object* v_snapshotTasks_3790_; lean_object* v_asyncMode_3791_; uint8_t v_logWrites_3792_; lean_object* v___x_3793_; 
v___x_3780_ = lean_st_ref_take(v___y_3779_);
v_toEnvExtension_3781_ = lean_ctor_get(v___x_3767_, 0);
v_env_3782_ = lean_ctor_get(v___x_3780_, 0);
lean_inc_ref(v_env_3782_);
v_nextMacroScope_3783_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_nextMacroScope_3783_);
v_ngen_3784_ = lean_ctor_get(v___x_3780_, 2);
lean_inc_ref(v_ngen_3784_);
v_auxDeclNGen_3785_ = lean_ctor_get(v___x_3780_, 3);
lean_inc_ref(v_auxDeclNGen_3785_);
v_traceState_3786_ = lean_ctor_get(v___x_3780_, 4);
lean_inc_ref(v_traceState_3786_);
v_recordedDeps_3787_ = lean_ctor_get(v___x_3780_, 6);
lean_inc_ref(v_recordedDeps_3787_);
v_messages_3788_ = lean_ctor_get(v___x_3780_, 7);
lean_inc_ref(v_messages_3788_);
v_infoState_3789_ = lean_ctor_get(v___x_3780_, 8);
lean_inc_ref(v_infoState_3789_);
v_snapshotTasks_3790_ = lean_ctor_get(v___x_3780_, 9);
lean_inc_ref(v_snapshotTasks_3790_);
lean_dec(v___x_3780_);
v_asyncMode_3791_ = lean_ctor_get(v_toEnvExtension_3781_, 2);
v_logWrites_3792_ = lean_ctor_get_uint8(v_toEnvExtension_3781_, sizeof(void*)*6);
v___x_3793_ = lean_box(0);
if (v_logWrites_3792_ == 0)
{
lean_object* v___x_3794_; 
lean_inc_ref(v_toEnvExtension_3781_);
v___x_3794_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3781_, v_env_3782_, v___f_3776_, v_asyncMode_3791_, v___x_3769_, v___x_3777_);
v___y_3745_ = v___y_3779_;
v___y_3746_ = v_infoState_3789_;
v___y_3747_ = v_messages_3788_;
v___y_3748_ = v_auxDeclNGen_3785_;
v___y_3749_ = v_ngen_3784_;
v___y_3750_ = v_nextMacroScope_3783_;
v___y_3751_ = v_traceState_3786_;
v___y_3752_ = v___x_3793_;
v___y_3753_ = v_snapshotTasks_3790_;
v___y_3754_ = v_recordedDeps_3787_;
v___y_3755_ = v___x_3794_;
goto v___jp_3744_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_inc_ref_n(v_toEnvExtension_3781_, 2);
v___x_3795_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3781_, v_env_3782_);
lean_dec_ref(v_env_3782_);
v___x_3796_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3781_, v___x_3795_, v___f_3776_, v_asyncMode_3791_, v___x_3769_, v___x_3777_);
v___y_3745_ = v___y_3779_;
v___y_3746_ = v_infoState_3789_;
v___y_3747_ = v_messages_3788_;
v___y_3748_ = v_auxDeclNGen_3785_;
v___y_3749_ = v_ngen_3784_;
v___y_3750_ = v_nextMacroScope_3783_;
v___y_3751_ = v_traceState_3786_;
v___y_3752_ = v___x_3793_;
v___y_3753_ = v_snapshotTasks_3790_;
v___y_3754_ = v_recordedDeps_3787_;
v___y_3755_ = v___x_3796_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec_ref_known(v_entry_3764_, 1);
lean_dec(v_hint_3740_);
lean_dec(v_mod_3738_);
v___x_3830_ = lean_box(0);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
v___jp_3744_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_3757_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3757_, 0, v___y_3755_);
lean_ctor_set(v___x_3757_, 1, v___y_3750_);
lean_ctor_set(v___x_3757_, 2, v___y_3749_);
lean_ctor_set(v___x_3757_, 3, v___y_3748_);
lean_ctor_set(v___x_3757_, 4, v___y_3751_);
lean_ctor_set(v___x_3757_, 5, v___x_3756_);
lean_ctor_set(v___x_3757_, 6, v___y_3754_);
lean_ctor_set(v___x_3757_, 7, v___y_3747_);
lean_ctor_set(v___x_3757_, 8, v___y_3746_);
lean_ctor_set(v___x_3757_, 9, v___y_3753_);
v___x_3758_ = lean_st_ref_put(v___y_3745_, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___y_3752_);
return v___x_3759_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_3738_ = stack[0].m_obj;
uint8_t v_isMeta_3739_ = stack[1].m_num;
lean_object* v_hint_3740_ = stack[2].m_obj;
lean_object* v___y_3741_ = stack[3].m_obj;
lean_object* v___y_3742_ = stack[4].m_obj;
lean_object* v_res_3832_;
v_res_3832_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3738_, v_isMeta_3739_, v_hint_3740_, v___y_3741_, v___y_3742_);
stack->m_obj
 = v_res_3832_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3833_, lean_object* v_isMeta_3834_, lean_object* v_hint_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
uint8_t v_isMeta_boxed_3839_; lean_object* v_res_3840_; 
v_isMeta_boxed_3839_ = lean_unbox(v_isMeta_3834_);
v_res_3840_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3833_, v_isMeta_boxed_3839_, v_hint_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3840_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3841_, lean_object* v_declName_3842_, lean_object* v_as_3843_, size_t v_sz_3844_, size_t v_i_3845_, lean_object* v_b_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_usize_dec_lt(v_i_3845_, v_sz_3844_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; 
lean_dec(v_declName_3842_);
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_b_3846_);
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; lean_object* v_modules_3853_; lean_object* v___x_3854_; lean_object* v_a_3855_; lean_object* v___x_3856_; lean_object* v_toImport_3857_; lean_object* v_module_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3852_ = l_Lean_Environment_header(v___x_3841_);
v_modules_3853_ = lean_ctor_get(v___x_3852_, 3);
lean_inc_ref(v_modules_3853_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3855_ = lean_array_uget_borrowed(v_as_3843_, v_i_3845_);
v___x_3856_ = lean_array_get(v___x_3854_, v_modules_3853_, v_a_3855_);
lean_dec_ref(v_modules_3853_);
v_toImport_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc_ref(v_toImport_3857_);
lean_dec(v___x_3856_);
v_module_3858_ = lean_ctor_get(v_toImport_3857_, 0);
lean_inc(v_module_3858_);
lean_dec_ref(v_toImport_3857_);
v___x_3859_ = lean_box(0);
v___x_3860_ = 0;
lean_inc(v_declName_3842_);
v___x_3861_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3858_, v___x_3860_, v_declName_3842_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3861_) == 0)
{
size_t v___x_3862_; size_t v___x_3863_; 
lean_dec_ref_known(v___x_3861_, 1);
v___x_3862_ = ((size_t)1ULL);
v___x_3863_ = lean_usize_add(v_i_3845_, v___x_3862_);
v_i_3845_ = v___x_3863_;
v_b_3846_ = v___x_3859_;
goto _start;
}
else
{
lean_dec(v_declName_3842_);
return v___x_3861_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3841_ = stack[0].m_obj;
lean_object* v_declName_3842_ = stack[1].m_obj;
lean_object* v_as_3843_ = stack[2].m_obj;
size_t v_sz_3844_ = stack[3].m_num;
size_t v_i_3845_ = stack[4].m_num;
lean_object* v_b_3846_ = stack[5].m_obj;
lean_object* v___y_3847_ = stack[6].m_obj;
lean_object* v___y_3848_ = stack[7].m_obj;
lean_object* v_res_3865_;
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3841_, v_declName_3842_, v_as_3843_, v_sz_3844_, v_i_3845_, v_b_3846_, v___y_3847_, v___y_3848_);
stack->m_obj
 = v_res_3865_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3866_, lean_object* v_declName_3867_, lean_object* v_as_3868_, lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3866_, v_declName_3867_, v_as_3868_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v_as_3868_);
lean_dec_ref(v___x_3866_);
return v_res_3877_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3878_, uint8_t v_isMeta_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_env_3888_; lean_object* v___y_3890_; lean_object* v___x_3903_; 
v___x_3883_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3884_ = lean_st_ref_get(v___y_3881_);
v_env_3888_ = lean_ctor_get(v___x_3884_, 0);
lean_inc_ref(v_env_3888_);
lean_dec(v___x_3884_);
v___x_3903_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3888_, v_declName_3878_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_dec_ref(v_env_3888_);
lean_dec(v_declName_3878_);
goto v___jp_3885_;
}
else
{
lean_object* v_val_3904_; lean_object* v___x_3905_; lean_object* v_modules_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v_val_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_val_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = l_Lean_Environment_header(v_env_3888_);
v_modules_3906_ = lean_ctor_get(v___x_3905_, 3);
lean_inc_ref(v_modules_3906_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = lean_array_get_size(v_modules_3906_);
v___x_3908_ = lean_nat_dec_lt(v_val_3904_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_dec_ref(v_modules_3906_);
lean_dec(v_val_3904_);
lean_dec_ref(v_env_3888_);
lean_dec(v_declName_3878_);
goto v___jp_3885_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___y_3912_; 
v___x_3909_ = lean_array_fget(v_modules_3906_, v_val_3904_);
lean_dec(v_val_3904_);
lean_dec_ref(v_modules_3906_);
v___x_3910_ = lean_st_ref_get(v___y_3881_);
if (v_isMeta_3879_ == 0)
{
lean_dec(v___x_3910_);
v___y_3912_ = v_isMeta_3879_;
goto v___jp_3911_;
}
else
{
lean_object* v_env_3923_; uint8_t v___x_3924_; 
v_env_3923_ = lean_ctor_get(v___x_3910_, 0);
lean_inc_ref(v_env_3923_);
lean_dec(v___x_3910_);
lean_inc(v_declName_3878_);
v___x_3924_ = l_Lean_isMarkedMeta(v_env_3923_, v_declName_3878_);
if (v___x_3924_ == 0)
{
v___y_3912_ = v_isMeta_3879_;
goto v___jp_3911_;
}
else
{
uint8_t v___x_3925_; 
v___x_3925_ = 0;
v___y_3912_ = v___x_3925_;
goto v___jp_3911_;
}
}
v___jp_3911_:
{
lean_object* v_toImport_3913_; lean_object* v_module_3914_; lean_object* v___x_3915_; 
v_toImport_3913_ = lean_ctor_get(v___x_3909_, 0);
lean_inc_ref(v_toImport_3913_);
lean_dec(v___x_3909_);
v_module_3914_ = lean_ctor_get(v_toImport_3913_, 0);
lean_inc(v_module_3914_);
lean_dec_ref(v_toImport_3913_);
lean_inc(v_declName_3878_);
v___x_3915_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3914_, v___y_3912_, v_declName_3878_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref_known(v___x_3915_, 1);
v___x_3916_ = l_Lean_indirectModUseExt;
v___x_3917_ = lean_box(1);
v___x_3918_ = lean_box(0);
lean_inc_ref(v_env_3888_);
v___x_3919_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3883_, v___x_3916_, v_env_3888_, v___x_3917_, v___x_3918_);
v___x_3920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3919_, v_declName_3878_);
lean_dec(v___x_3919_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3890_ = v___x_3921_;
goto v___jp_3889_;
}
else
{
lean_object* v_val_3922_; 
v_val_3922_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_val_3922_);
lean_dec_ref_known(v___x_3920_, 1);
v___y_3890_ = v_val_3922_;
goto v___jp_3889_;
}
}
else
{
lean_dec_ref(v_env_3888_);
lean_dec(v_declName_3878_);
return v___x_3915_;
}
}
}
}
v___jp_3885_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
v___jp_3889_:
{
lean_object* v___x_3891_; size_t v_sz_3892_; size_t v___x_3893_; lean_object* v___x_3894_; 
v___x_3891_ = lean_box(0);
v_sz_3892_ = lean_array_size(v___y_3890_);
v___x_3893_ = ((size_t)0ULL);
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3888_, v_declName_3878_, v___y_3890_, v_sz_3892_, v___x_3893_, v___x_3891_, v___y_3880_, v___y_3881_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v_env_3888_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v___x_3894_, 0);
lean_dec(v_unused_3902_);
v___x_3896_ = v___x_3894_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_dec(v___x_3894_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3891_);
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3891_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
else
{
return v___x_3894_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3878_ = stack[0].m_obj;
uint8_t v_isMeta_3879_ = stack[1].m_num;
lean_object* v___y_3880_ = stack[2].m_obj;
lean_object* v___y_3881_ = stack[3].m_obj;
lean_object* v_res_3926_;
v_res_3926_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3878_, v_isMeta_3879_, v___y_3880_, v___y_3881_);
stack->m_obj
 = v_res_3926_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3927_, lean_object* v_isMeta_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v_isMeta_boxed_3932_; lean_object* v_res_3933_; 
v_isMeta_boxed_3932_ = lean_unbox(v_isMeta_3928_);
v_res_3933_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3927_, v_isMeta_boxed_3932_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
return v_res_3933_;
}
}
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3939_ = lean_st_ref_get(v___x_3938_);
v___x_3940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3939_, v_attrName_3934_);
lean_dec(v___x_3939_);
if (lean_obj_tag(v___x_3940_) == 1)
{
lean_object* v_val_3941_; lean_object* v_ext_3942_; lean_object* v_name_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; 
v_val_3941_ = lean_ctor_get(v___x_3940_, 0);
v_ext_3942_ = lean_ctor_get(v_val_3941_, 1);
v_name_3943_ = lean_ctor_get(v_ext_3942_, 1);
v___x_3944_ = 1;
lean_inc(v_name_3943_);
v___x_3945_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3943_, v___x_3944_, v_a_3935_, v_a_3936_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; 
v_unused_3953_ = lean_ctor_get(v___x_3945_, 0);
lean_dec(v_unused_3953_);
v___x_3947_ = v___x_3945_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_dec(v___x_3945_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3940_);
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3940_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref_known(v___x_3940_, 1);
v_a_3954_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3945_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3945_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3940_);
return v___x_3962_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getExtension_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_3934_ = stack[0].m_obj;
lean_object* v_a_3935_ = stack[1].m_obj;
lean_object* v_a_3936_ = stack[2].m_obj;
lean_object* v_res_3963_;
v_res_3963_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3934_, v_a_3935_, v_a_3936_);
stack->m_obj
 = v_res_3963_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3964_, v_a_3965_, v_a_3966_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_attrName_3964_);
return v_res_3968_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3970_, lean_object* v_x_3971_){
_start:
{
if (lean_obj_tag(v_x_3971_) == 0)
{
return v_x_3970_;
}
else
{
lean_object* v_key_3972_; lean_object* v_value_3973_; lean_object* v_tail_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4000_; 
v_key_3972_ = lean_ctor_get(v_x_3971_, 0);
v_value_3973_ = lean_ctor_get(v_x_3971_, 1);
v_tail_3974_ = lean_ctor_get(v_x_3971_, 2);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_x_3971_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3976_ = v_x_3971_;
v_isShared_3977_ = v_isSharedCheck_4000_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_tail_3974_);
lean_inc(v_value_3973_);
lean_inc(v_key_3972_);
lean_dec(v_x_3971_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4000_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; uint64_t v___y_3980_; 
v___x_3978_ = lean_array_get_size(v_x_3970_);
if (lean_obj_tag(v_key_3972_) == 0)
{
uint64_t v___x_3998_; 
v___x_3998_ = 1723ULL;
v___y_3980_ = v___x_3998_;
goto v___jp_3979_;
}
else
{
uint64_t v_hash_3999_; 
v_hash_3999_ = lean_ctor_get_uint64(v_key_3972_, sizeof(void*)*2);
v___y_3980_ = v_hash_3999_;
goto v___jp_3979_;
}
v___jp_3979_:
{
uint64_t v___x_3981_; uint64_t v___x_3982_; uint64_t v_fold_3983_; uint64_t v___x_3984_; uint64_t v___x_3985_; uint64_t v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3981_ = 32ULL;
v___x_3982_ = lean_uint64_shift_right(v___y_3980_, v___x_3981_);
v_fold_3983_ = lean_uint64_xor(v___y_3980_, v___x_3982_);
v___x_3984_ = 16ULL;
v___x_3985_ = lean_uint64_shift_right(v_fold_3983_, v___x_3984_);
v___x_3986_ = lean_uint64_xor(v_fold_3983_, v___x_3985_);
v___x_3987_ = lean_uint64_to_usize(v___x_3986_);
v___x_3988_ = lean_usize_of_nat(v___x_3978_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_sub(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_usize_land(v___x_3987_, v___x_3990_);
v___x_3992_ = lean_array_uget_borrowed(v_x_3970_, v___x_3991_);
lean_inc(v___x_3992_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 2, v___x_3992_);
v___x_3994_ = v___x_3976_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_key_3972_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_value_3973_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_array_uset(v_x_3970_, v___x_3991_, v___x_3994_);
v_x_3970_ = v___x_3995_;
v_x_3971_ = v_tail_3974_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4001_, lean_object* v_source_4002_, lean_object* v_target_4003_){
_start:
{
lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4004_ = lean_array_get_size(v_source_4002_);
v___x_4005_ = lean_nat_dec_lt(v_i_4001_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_dec_ref(v_source_4002_);
lean_dec(v_i_4001_);
return v_target_4003_;
}
else
{
lean_object* v_es_4006_; lean_object* v___x_4007_; lean_object* v_source_4008_; lean_object* v_target_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_es_4006_ = lean_array_fget(v_source_4002_, v_i_4001_);
v___x_4007_ = lean_box(0);
v_source_4008_ = lean_array_fset(v_source_4002_, v_i_4001_, v___x_4007_);
v_target_4009_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4003_, v_es_4006_);
v___x_4010_ = lean_unsigned_to_nat(1u);
v___x_4011_ = lean_nat_add(v_i_4001_, v___x_4010_);
lean_dec(v_i_4001_);
v_i_4001_ = v___x_4011_;
v_source_4002_ = v_source_4008_;
v_target_4003_ = v_target_4009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4013_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_nbuckets_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4014_ = lean_array_get_size(v_data_4013_);
v___x_4015_ = lean_unsigned_to_nat(2u);
v_nbuckets_4016_ = lean_nat_mul(v___x_4014_, v___x_4015_);
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_box(0);
v___x_4019_ = lean_mk_array(v_nbuckets_4016_, v___x_4018_);
v___x_4020_ = lean_array_propagate_mark(v_data_4013_, v___x_4019_);
v___x_4021_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4017_, v_data_4013_, v___x_4020_);
return v___x_4021_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4022_, lean_object* v_x_4023_){
_start:
{
if (lean_obj_tag(v_x_4023_) == 0)
{
uint8_t v___x_4024_; 
v___x_4024_ = 0;
return v___x_4024_;
}
else
{
lean_object* v_key_4025_; lean_object* v_tail_4026_; uint8_t v___x_4027_; 
v_key_4025_ = lean_ctor_get(v_x_4023_, 0);
v_tail_4026_ = lean_ctor_get(v_x_4023_, 2);
v___x_4027_ = lean_name_eq(v_key_4025_, v_a_4022_);
if (v___x_4027_ == 0)
{
v_x_4023_ = v_tail_4026_;
goto _start;
}
else
{
return v___x_4027_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4022_ = stack[0].m_obj;
lean_object* v_x_4023_ = stack[1].m_obj;
uint8_t v_res_4029_;
v_res_4029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4022_, v_x_4023_);
stack->m_num = v_res_4029_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4030_, lean_object* v_x_4031_){
_start:
{
uint8_t v_res_4032_; lean_object* v_r_4033_; 
v_res_4032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4030_, v_x_4031_);
lean_dec(v_x_4031_);
lean_dec(v_a_4030_);
v_r_4033_ = lean_box(v_res_4032_);
return v_r_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4034_, lean_object* v_b_4035_, lean_object* v_x_4036_){
_start:
{
if (lean_obj_tag(v_x_4036_) == 0)
{
lean_dec(v_b_4035_);
lean_dec(v_a_4034_);
return v_x_4036_;
}
else
{
lean_object* v_key_4037_; lean_object* v_value_4038_; lean_object* v_tail_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4051_; 
v_key_4037_ = lean_ctor_get(v_x_4036_, 0);
v_value_4038_ = lean_ctor_get(v_x_4036_, 1);
v_tail_4039_ = lean_ctor_get(v_x_4036_, 2);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_x_4036_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4041_ = v_x_4036_;
v_isShared_4042_ = v_isSharedCheck_4051_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_tail_4039_);
lean_inc(v_value_4038_);
lean_inc(v_key_4037_);
lean_dec(v_x_4036_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4051_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_name_eq(v_key_4037_, v_a_4034_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4034_, v_b_4035_, v_tail_4039_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 2, v___x_4044_);
v___x_4046_ = v___x_4041_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_key_4037_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v_value_4038_);
lean_ctor_set(v_reuseFailAlloc_4047_, 2, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
else
{
lean_object* v___x_4049_; 
lean_dec(v_value_4038_);
lean_dec(v_key_4037_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 1, v_b_4035_);
lean_ctor_set(v___x_4041_, 0, v_a_4034_);
v___x_4049_ = v___x_4041_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4034_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_b_4035_);
lean_ctor_set(v_reuseFailAlloc_4050_, 2, v_tail_4039_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4052_, lean_object* v_a_4053_, lean_object* v_b_4054_){
_start:
{
lean_object* v_size_4055_; lean_object* v_buckets_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4102_; 
v_size_4055_ = lean_ctor_get(v_m_4052_, 0);
v_buckets_4056_ = lean_ctor_get(v_m_4052_, 1);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_m_4052_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4058_ = v_m_4052_;
v_isShared_4059_ = v_isSharedCheck_4102_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_buckets_4056_);
lean_inc(v_size_4055_);
lean_dec(v_m_4052_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4102_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; uint64_t v___y_4062_; 
v___x_4060_ = lean_array_get_size(v_buckets_4056_);
if (lean_obj_tag(v_a_4053_) == 0)
{
uint64_t v___x_4100_; 
v___x_4100_ = 1723ULL;
v___y_4062_ = v___x_4100_;
goto v___jp_4061_;
}
else
{
uint64_t v_hash_4101_; 
v_hash_4101_ = lean_ctor_get_uint64(v_a_4053_, sizeof(void*)*2);
v___y_4062_ = v_hash_4101_;
goto v___jp_4061_;
}
v___jp_4061_:
{
uint64_t v___x_4063_; uint64_t v___x_4064_; uint64_t v_fold_4065_; uint64_t v___x_4066_; uint64_t v___x_4067_; uint64_t v___x_4068_; size_t v___x_4069_; size_t v___x_4070_; size_t v___x_4071_; size_t v___x_4072_; size_t v___x_4073_; lean_object* v_bkt_4074_; uint8_t v___x_4075_; 
v___x_4063_ = 32ULL;
v___x_4064_ = lean_uint64_shift_right(v___y_4062_, v___x_4063_);
v_fold_4065_ = lean_uint64_xor(v___y_4062_, v___x_4064_);
v___x_4066_ = 16ULL;
v___x_4067_ = lean_uint64_shift_right(v_fold_4065_, v___x_4066_);
v___x_4068_ = lean_uint64_xor(v_fold_4065_, v___x_4067_);
v___x_4069_ = lean_uint64_to_usize(v___x_4068_);
v___x_4070_ = lean_usize_of_nat(v___x_4060_);
v___x_4071_ = ((size_t)1ULL);
v___x_4072_ = lean_usize_sub(v___x_4070_, v___x_4071_);
v___x_4073_ = lean_usize_land(v___x_4069_, v___x_4072_);
v_bkt_4074_ = lean_array_uget_borrowed(v_buckets_4056_, v___x_4073_);
v___x_4075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4053_, v_bkt_4074_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; lean_object* v_size_x27_4077_; lean_object* v___x_4078_; lean_object* v_buckets_x27_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v___x_4076_ = lean_unsigned_to_nat(1u);
v_size_x27_4077_ = lean_nat_add(v_size_4055_, v___x_4076_);
lean_dec(v_size_4055_);
lean_inc(v_bkt_4074_);
v___x_4078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4053_);
lean_ctor_set(v___x_4078_, 1, v_b_4054_);
lean_ctor_set(v___x_4078_, 2, v_bkt_4074_);
v_buckets_x27_4079_ = lean_array_uset(v_buckets_4056_, v___x_4073_, v___x_4078_);
v___x_4080_ = lean_unsigned_to_nat(4u);
v___x_4081_ = lean_nat_mul(v_size_x27_4077_, v___x_4080_);
v___x_4082_ = lean_unsigned_to_nat(3u);
v___x_4083_ = lean_nat_div(v___x_4081_, v___x_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_array_get_size(v_buckets_x27_4079_);
v___x_4085_ = lean_nat_dec_le(v___x_4083_, v___x_4084_);
lean_dec(v___x_4083_);
if (v___x_4085_ == 0)
{
lean_object* v_val_4086_; lean_object* v___x_4088_; 
v_val_4086_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4079_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v_val_4086_);
lean_ctor_set(v___x_4058_, 0, v_size_x27_4077_);
v___x_4088_ = v___x_4058_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_size_x27_4077_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_val_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
else
{
lean_object* v___x_4091_; 
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v_buckets_x27_4079_);
lean_ctor_set(v___x_4058_, 0, v_size_x27_4077_);
v___x_4091_ = v___x_4058_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_size_x27_4077_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_buckets_x27_4079_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
else
{
lean_object* v___x_4093_; lean_object* v_buckets_x27_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4098_; 
lean_inc(v_bkt_4074_);
v___x_4093_ = lean_box(0);
v_buckets_x27_4094_ = lean_array_uset(v_buckets_4056_, v___x_4073_, v___x_4093_);
v___x_4095_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4053_, v_b_4054_, v_bkt_4074_);
v___x_4096_ = lean_array_uset(v_buckets_x27_4094_, v___x_4073_, v___x_4095_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4096_);
v___x_4098_ = v___x_4058_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_size_4055_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4096_);
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
lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4103_, lean_object* v_ref_4104_){
_start:
{
lean_object* v___x_4106_; 
lean_inc(v_ref_4104_);
v___x_4106_ = l_Lean_Meta_Grind_mkExtension(v_ref_4104_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; uint8_t v___x_4108_; uint8_t v___x_4109_; lean_object* v___x_4110_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc_n(v_a_4107_, 2);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = 0;
v___x_4109_ = 1;
lean_inc(v_ref_4104_);
lean_inc(v_attrName_4103_);
v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4103_, v___x_4108_, v___x_4109_, v_a_4107_, v_ref_4104_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4110_, 1);
lean_inc(v_ref_4104_);
lean_inc(v_a_4107_);
lean_inc(v_attrName_4103_);
v___x_4111_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4103_, v___x_4108_, v___x_4108_, v_a_4107_, v_ref_4104_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v___x_4112_; 
lean_dec_ref_known(v___x_4111_, 1);
lean_inc(v_ref_4104_);
lean_inc(v_a_4107_);
lean_inc(v_attrName_4103_);
v___x_4112_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4103_, v___x_4109_, v___x_4109_, v_a_4107_, v_ref_4104_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v___x_4113_; 
lean_dec_ref_known(v___x_4112_, 1);
lean_inc(v_a_4107_);
lean_inc(v_attrName_4103_);
v___x_4113_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4103_, v___x_4109_, v___x_4108_, v_a_4107_, v_ref_4104_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4124_; 
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; 
v_unused_4125_ = lean_ctor_get(v___x_4113_, 0);
lean_dec(v_unused_4125_);
v___x_4115_ = v___x_4113_;
v_isShared_4116_ = v_isSharedCheck_4124_;
goto v_resetjp_4114_;
}
else
{
lean_dec(v___x_4113_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4124_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4117_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4118_ = lean_st_ref_take(v___x_4117_);
lean_inc(v_a_4107_);
v___x_4119_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4118_, v_attrName_4103_, v_a_4107_);
v___x_4120_ = lean_st_ref_put(v___x_4117_, v___x_4119_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v_a_4107_);
v___x_4122_ = v___x_4115_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4107_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_a_4107_);
lean_dec(v_attrName_4103_);
v_a_4126_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4113_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4113_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_a_4107_);
lean_dec(v_ref_4104_);
lean_dec(v_attrName_4103_);
v_a_4134_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4112_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4112_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_a_4107_);
lean_dec(v_ref_4104_);
lean_dec(v_attrName_4103_);
v_a_4142_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4111_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4111_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v_a_4107_);
lean_dec(v_ref_4104_);
lean_dec(v_attrName_4103_);
v_a_4150_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4110_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4110_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_dec(v_ref_4104_);
lean_dec(v_attrName_4103_);
return v___x_4106_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_registerAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4103_ = stack[0].m_obj;
lean_object* v_ref_4104_ = stack[1].m_obj;
lean_object* v_res_4158_;
v_res_4158_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4103_, v_ref_4104_);
stack->m_obj
 = v_res_4158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4159_, lean_object* v_ref_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4159_, v_ref_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4163_, lean_object* v_m_4164_, lean_object* v_a_4165_, lean_object* v_b_4166_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4164_, v_a_4165_, v_b_4166_);
return v___x_4167_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4168_, lean_object* v_a_4169_, lean_object* v_x_4170_){
_start:
{
uint8_t v___x_4171_; 
v___x_4171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4169_, v_x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4169_ = stack[1].m_obj;
lean_object* v_x_4170_ = stack[2].m_obj;
uint8_t v_res_4172_;
v_res_4172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_box(0), v_a_4169_, v_x_4170_);
stack->m_num = v_res_4172_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4173_, lean_object* v_a_4174_, lean_object* v_x_4175_){
_start:
{
uint8_t v_res_4176_; lean_object* v_r_4177_; 
v_res_4176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4173_, v_a_4174_, v_x_4175_);
lean_dec(v_x_4175_);
lean_dec(v_a_4174_);
v_r_4177_ = lean_box(v_res_4176_);
return v_r_4177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4178_, lean_object* v_data_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4181_, lean_object* v_a_4182_, lean_object* v_b_4183_, lean_object* v_x_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4182_, v_b_4183_, v_x_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4186_, lean_object* v_i_4187_, lean_object* v_source_4188_, lean_object* v_target_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4187_, v_source_4188_, v_target_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4191_, lean_object* v_x_4192_, lean_object* v_x_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4192_, v_x_4193_);
return v___x_4194_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4203_ = l_Lean_Meta_Grind_registerAttr(v___x_4201_, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4204_;
v_res_4204_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4206_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4219_ = l_Lean_Meta_Grind_registerAttr(v___x_4217_, v___x_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4220_;
v_res_4220_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4220_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4222_;
}
}
lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v_env_4228_; lean_object* v___x_4229_; lean_object* v_ext_4230_; lean_object* v_toEnvExtension_4231_; lean_object* v_asyncMode_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v_casesTypes_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4226_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4227_ = lean_st_ref_get(v_a_4224_);
v_env_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc_ref(v_env_4228_);
lean_dec(v___x_4227_);
v___x_4229_ = l_Lean_Meta_Grind_grindExt;
v_ext_4230_ = lean_ctor_get(v___x_4229_, 1);
v_toEnvExtension_4231_ = lean_ctor_get(v_ext_4230_, 0);
v_asyncMode_4232_ = lean_ctor_get(v_toEnvExtension_4231_, 2);
v___x_4233_ = 0;
v___x_4234_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4226_, v___x_4229_, v_env_4228_, v_asyncMode_4232_, v___x_4233_);
v_casesTypes_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc_ref(v_casesTypes_4235_);
lean_dec(v___x_4234_);
v___x_4236_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4235_, v_declName_4223_);
lean_dec_ref(v_casesTypes_4235_);
v___x_4237_ = lean_box(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isGlobalSplit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4223_ = stack[0].m_obj;
lean_object* v_a_4224_ = stack[1].m_obj;
lean_object* v_res_4239_;
v_res_4239_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4223_, v_a_4224_);
stack->m_obj
 = v_res_4239_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4240_, v_a_4241_);
lean_dec(v_a_4241_);
lean_dec(v_declName_4240_);
return v_res_4243_;
}
}
lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4244_, v_a_4246_);
return v___x_4248_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isGlobalSplit_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4244_ = stack[0].m_obj;
lean_object* v_a_4245_ = stack[1].m_obj;
lean_object* v_a_4246_ = stack[2].m_obj;
lean_object* v_res_4249_;
v_res_4249_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4244_, v_a_4245_, v_a_4246_);
stack->m_obj
 = v_res_4249_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4250_, v_a_4251_, v_a_4252_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_declName_4250_);
return v_res_4254_;
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
