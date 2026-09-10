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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object* v_x_15_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
case 1:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1u);
return v___x_17_;
}
case 2:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(2u);
return v___x_18_;
}
case 3:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(3u);
return v___x_19_;
}
case 4:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(4u);
return v___x_20_;
}
case 5:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(5u);
return v___x_21_;
}
case 6:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(6u);
return v___x_22_;
}
case 7:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(7u);
return v___x_23_;
}
case 8:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(8u);
return v___x_24_;
}
case 9:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(9u);
return v___x_25_;
}
case 10:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(10u);
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(11u);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
switch(lean_obj_tag(v_t_30_))
{
case 0:
{
lean_object* v_k_32_; lean_object* v___x_33_; 
v_k_32_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_k_32_);
lean_dec_ref_known(v_t_30_, 1);
v___x_33_ = lean_apply_1(v_k_31_, v_k_32_);
return v___x_33_;
}
case 1:
{
uint8_t v_eager_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_eager_34_ = lean_ctor_get_uint8(v_t_30_, 0);
lean_dec_ref_known(v_t_30_, 0);
v___x_35_ = lean_box(v_eager_34_);
v___x_36_ = lean_apply_1(v_k_31_, v___x_35_);
return v___x_36_;
}
case 5:
{
lean_object* v_prio_37_; lean_object* v___x_38_; 
v_prio_37_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_prio_37_);
lean_dec_ref_known(v_t_30_, 1);
v___x_38_ = lean_apply_1(v_k_31_, v_prio_37_);
return v___x_38_;
}
case 8:
{
uint8_t v_post_39_; uint8_t v_inv_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_post_39_ = lean_ctor_get_uint8(v_t_30_, 0);
v_inv_40_ = lean_ctor_get_uint8(v_t_30_, 1);
lean_dec_ref_known(v_t_30_, 0);
v___x_41_ = lean_box(v_post_39_);
v___x_42_ = lean_box(v_inv_40_);
v___x_43_ = lean_apply_2(v_k_31_, v___x_41_, v___x_42_);
return v___x_43_;
}
default: 
{
lean_dec(v_t_30_);
return v_k_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_46_, v_k_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_50_, v_ctorIdx_51_, v_t_52_, v_h_53_, v_k_54_);
lean_dec(v_ctorIdx_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_56_, lean_object* v_ematch_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_56_, v_ematch_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_ematch_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_60_, v_ematch_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_64_, lean_object* v_cases_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_64_, v_cases_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_cases_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_68_, v_cases_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_72_, lean_object* v_intro_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_72_, v_intro_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_intro_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_76_, v_intro_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_80_, lean_object* v_infer_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_80_, v_infer_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_infer_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_84_, v_infer_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_88_, lean_object* v_ext_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_88_, v_ext_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_ext_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_92_, v_ext_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_96_, lean_object* v_symbol_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_96_, v_symbol_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_symbol_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_100_, v_symbol_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_104_, lean_object* v_inj_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_104_, v_inj_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_inj_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_108_, v_inj_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_112_, lean_object* v_funCC_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_112_, v_funCC_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_funCC_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_116_, v_funCC_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_120_, lean_object* v_norm_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_120_, v_norm_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_norm_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_124_, v_norm_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_128_, lean_object* v_unfold_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_128_, v_unfold_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_unfold_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_132_, v_unfold_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_136_, lean_object* v_homo_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_136_, v_homo_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_homo_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_140_, v_homo_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_144_, lean_object* v_homoPred_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_144_, v_homoPred_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_homoPred_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_148_, v_homoPred_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
lean_ctor_set(v___x_157_, 10, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_toCold_176_; lean_object* v_env_177_; lean_object* v_options_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_toCold_176_ = lean_ctor_get(v___y_172_, 0);
v_env_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_175_);
v_options_178_ = lean_ctor_get(v_toCold_176_, 2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_178_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_177_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v_options_178_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_171_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_189_, v___y_190_, v___y_191_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_ref_193_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_ref_193_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_toCold_214_; lean_object* v_currRecDepth_215_; lean_object* v_ref_216_; uint8_t v_diag_217_; uint8_t v_suppressElabErrors_218_; lean_object* v_ref_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_toCold_214_ = lean_ctor_get(v___y_211_, 0);
v_currRecDepth_215_ = lean_ctor_get(v___y_211_, 1);
v_ref_216_ = lean_ctor_get(v___y_211_, 2);
v_diag_217_ = lean_ctor_get_uint8(v___y_211_, sizeof(void*)*3);
v_suppressElabErrors_218_ = lean_ctor_get_uint8(v___y_211_, sizeof(void*)*3 + 1);
v_ref_219_ = l_Lean_replaceRef(v_ref_209_, v_ref_216_);
lean_inc(v_currRecDepth_215_);
lean_inc_ref(v_toCold_214_);
v___x_220_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_220_, 0, v_toCold_214_);
lean_ctor_set(v___x_220_, 1, v_currRecDepth_215_);
lean_ctor_set(v___x_220_, 2, v_ref_219_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*3, v_diag_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*3 + 1, v_suppressElabErrors_218_);
v___x_221_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_210_, v___x_220_, v___y_212_);
lean_dec_ref_known(v___x_220_, 3);
return v___x_221_;
}
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
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_404_);
v___x_409_ = l_Lean_Syntax_isOfKind(v_stx_404_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_411_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_414_, v_a_405_, v_a_406_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_Lean_Syntax_getArg(v_stx_404_, v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_417_);
v___x_419_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_417_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_417_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_417_);
v___x_425_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_417_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_417_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_417_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_417_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_417_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_417_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_417_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_417_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_417_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_417_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_417_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_417_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_417_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_417_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_417_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_417_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_417_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_417_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v___x_417_);
v___x_462_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_463_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_466_, v_a_405_, v_a_406_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_stx_404_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v___x_417_, v___x_468_);
lean_dec(v___x_417_);
v___x_470_ = l_Lean_Syntax_isNatLit_x3f(v___x_469_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
lean_dec(v___x_469_);
v_val_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 5);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_val_471_);
v___x_476_ = v_reuseFailAlloc_478_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v___x_470_);
v___x_480_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__53, &l_Lean_Meta_Grind_getAttrKindCore___closed__53_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53);
v___x_481_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_469_, v___x_480_, v_a_405_, v_a_406_);
lean_dec(v___x_469_);
return v___x_481_;
}
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_482_ = lean_box(11);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_484_ = lean_box(10);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_486_ = lean_box(9);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = l_Lean_Syntax_getArg(v___x_417_, v___x_488_);
lean_inc(v___x_489_);
v___x_490_ = l_Lean_Syntax_matchesNull(v___x_489_, v___x_416_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
lean_inc(v___x_489_);
v___x_491_ = l_Lean_Syntax_matchesNull(v___x_489_, v___x_488_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_489_);
lean_dec(v___x_417_);
v___x_492_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_493_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_496_, v_a_405_, v_a_406_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = l_Lean_Syntax_getArg(v___x_489_, v___x_416_);
lean_dec(v___x_489_);
v___x_499_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_498_);
v___x_500_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_502_ = l_Lean_Syntax_isOfKind(v___x_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_417_);
v___x_503_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_504_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_507_, v_a_405_, v_a_406_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_unsigned_to_nat(2u);
v___x_510_ = l_Lean_Syntax_getArg(v___x_417_, v___x_509_);
lean_dec(v___x_417_);
lean_inc(v___x_510_);
v___x_511_ = l_Lean_Syntax_matchesNull(v___x_510_, v___x_416_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_Syntax_matchesNull(v___x_510_, v___x_488_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_514_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_517_, v_a_405_, v_a_406_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_stx_404_);
v___x_519_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_519_, 0, v___x_511_);
lean_ctor_set_uint8(v___x_519_, 1, v___x_409_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_510_);
lean_dec(v_stx_404_);
v___x_521_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_521_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_521_, 1, v___x_500_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_dec(v___x_498_);
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = l_Lean_Syntax_getArg(v___x_417_, v___x_523_);
lean_dec(v___x_417_);
lean_inc(v___x_524_);
v___x_525_ = l_Lean_Syntax_matchesNull(v___x_524_, v___x_416_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Syntax_matchesNull(v___x_524_, v___x_488_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_528_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_531_, v_a_405_, v_a_406_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_stx_404_);
v___x_533_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_533_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_533_, 1, v___x_409_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_524_);
lean_dec(v_stx_404_);
v___x_535_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_535_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_535_, 1, v___x_490_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
lean_dec(v___x_489_);
v___x_537_ = lean_unsigned_to_nat(2u);
v___x_538_ = l_Lean_Syntax_getArg(v___x_417_, v___x_537_);
lean_dec(v___x_417_);
lean_inc(v___x_538_);
v___x_539_ = l_Lean_Syntax_matchesNull(v___x_538_, v___x_416_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Syntax_matchesNull(v___x_538_, v___x_488_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_542_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_545_, v_a_405_, v_a_406_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_stx_404_);
v___x_547_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_547_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_547_, 1, v___x_409_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_538_);
lean_dec(v_stx_404_);
v___x_549_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_549_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_549_, 1, v___x_451_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_551_ = lean_box(7);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_553_ = lean_box(6);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_555_ = lean_box(4);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_557_ = lean_box(2);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_559_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_559_, 0, v___x_409_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_561_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_561_, 0, v___x_439_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_563_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_563_, 0, v___x_409_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_566_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_568_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_570_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_572_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(3u);
v___x_575_ = l_Lean_Syntax_getArg(v___x_417_, v___x_574_);
lean_dec(v___x_417_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_416_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_575_);
v___x_578_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_575_);
v___x_579_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_580_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_583_, v_a_405_, v_a_406_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = l_Lean_Syntax_getArg(v___x_575_, v___x_416_);
lean_dec(v___x_575_);
v___x_586_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_587_ = l_Lean_Syntax_isOfKind(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_588_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_589_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_592_, v_a_405_, v_a_406_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_stx_404_);
v___x_594_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_594_, 0, v___x_409_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_575_);
lean_dec(v_stx_404_);
v___x_597_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_597_, 0, v___x_427_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(2u);
v___x_601_ = l_Lean_Syntax_getArg(v___x_417_, v___x_600_);
lean_dec(v___x_417_);
lean_inc(v___x_601_);
v___x_602_ = l_Lean_Syntax_matchesNull(v___x_601_, v___x_416_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_601_);
v___x_604_ = l_Lean_Syntax_matchesNull(v___x_601_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_601_);
v___x_605_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_606_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_609_, v_a_405_, v_a_406_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = l_Lean_Syntax_getArg(v___x_601_, v___x_416_);
lean_dec(v___x_601_);
v___x_612_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_613_ = l_Lean_Syntax_isOfKind(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_615_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_618_, v_a_405_, v_a_406_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_stx_404_);
v___x_620_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_620_, 0, v___x_409_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_601_);
lean_dec(v_stx_404_);
v___x_623_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_623_, 0, v___x_425_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = l_Lean_Syntax_getArg(v___x_417_, v___x_626_);
lean_dec(v___x_417_);
lean_inc(v___x_627_);
v___x_628_ = l_Lean_Syntax_matchesNull(v___x_627_, v___x_416_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
lean_inc(v___x_627_);
v___x_629_ = l_Lean_Syntax_matchesNull(v___x_627_, v___x_626_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_627_);
v___x_630_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_631_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_634_, v_a_405_, v_a_406_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = l_Lean_Syntax_getArg(v___x_627_, v___x_416_);
lean_dec(v___x_627_);
v___x_637_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_638_ = l_Lean_Syntax_isOfKind(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_640_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_643_, v_a_405_, v_a_406_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_stx_404_);
v___x_645_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_645_, 0, v___x_409_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v___x_627_);
lean_dec(v_stx_404_);
v___x_648_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_648_, 0, v___x_423_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v___x_417_);
lean_dec(v_stx_404_);
v___x_651_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = l_Lean_Syntax_getArg(v___x_417_, v___x_653_);
lean_dec(v___x_417_);
lean_inc(v___x_654_);
v___x_655_ = l_Lean_Syntax_matchesNull(v___x_654_, v___x_416_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v___x_654_);
v___x_656_ = l_Lean_Syntax_matchesNull(v___x_654_, v___x_653_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v___x_654_);
v___x_657_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_658_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_661_, v_a_405_, v_a_406_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = l_Lean_Syntax_getArg(v___x_654_, v___x_416_);
lean_dec(v___x_654_);
v___x_664_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_665_ = l_Lean_Syntax_isOfKind(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_667_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_670_, v_a_405_, v_a_406_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_stx_404_);
v___x_672_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_672_, 0, v___x_409_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_654_);
lean_dec(v_stx_404_);
v___x_675_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_675_, 0, v___x_419_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = l_Lean_Syntax_getArg(v___x_417_, v___x_678_);
lean_dec(v___x_417_);
lean_inc(v___x_679_);
v___x_680_ = l_Lean_Syntax_matchesNull(v___x_679_, v___x_416_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; 
lean_inc(v___x_679_);
v___x_681_ = l_Lean_Syntax_matchesNull(v___x_679_, v___x_678_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___x_679_);
v___x_682_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_683_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_686_, v_a_405_, v_a_406_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = l_Lean_Syntax_getArg(v___x_679_, v___x_416_);
lean_dec(v___x_679_);
v___x_689_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_690_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_692_ = l_Lean_MessageData_ofSyntax(v_stx_404_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_695_, v_a_405_, v_a_406_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_stx_404_);
v___x_697_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_697_, 0, v___x_409_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec(v___x_679_);
lean_dec(v_stx_404_);
v___x_700_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_713_, lean_object* v_msg_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_713_, v_msg_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_719_, lean_object* v_ref_720_, lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_720_, v_msg_721_, v___y_722_, v___y_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_726_, lean_object* v_ref_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_726_, v_ref_727_, v_msg_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v_ref_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_737_);
v___x_739_ = l_Lean_Syntax_isNone(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Lean_Syntax_getArg(v___x_738_, v___x_740_);
lean_dec(v___x_738_);
v___x_742_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_741_, v_a_734_, v_a_735_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v___x_738_);
v___x_743_ = lean_box(3);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_stx_745_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_757_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_756_, v_a_753_, v_a_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_763_, v_a_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_772_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_777_, lean_object* v_b_778_, uint8_t v_kind_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_toCold_783_; lean_object* v_currNamespace_784_; lean_object* v___x_785_; lean_object* v_env_786_; lean_object* v_nextMacroScope_787_; lean_object* v_ngen_788_; lean_object* v_auxDeclNGen_789_; lean_object* v_traceState_790_; lean_object* v_messages_791_; lean_object* v_infoState_792_; lean_object* v_snapshotTasks_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_805_; 
v_toCold_783_ = lean_ctor_get(v___y_780_, 0);
v_currNamespace_784_ = lean_ctor_get(v_toCold_783_, 4);
v___x_785_ = lean_st_ref_take(v___y_781_);
v_env_786_ = lean_ctor_get(v___x_785_, 0);
v_nextMacroScope_787_ = lean_ctor_get(v___x_785_, 1);
v_ngen_788_ = lean_ctor_get(v___x_785_, 2);
v_auxDeclNGen_789_ = lean_ctor_get(v___x_785_, 3);
v_traceState_790_ = lean_ctor_get(v___x_785_, 4);
v_messages_791_ = lean_ctor_get(v___x_785_, 6);
v_infoState_792_ = lean_ctor_get(v___x_785_, 7);
v_snapshotTasks_793_ = lean_ctor_get(v___x_785_, 8);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_785_, 5);
lean_dec(v_unused_806_);
v___x_795_ = v___x_785_;
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snapshotTasks_793_);
lean_inc(v_infoState_792_);
lean_inc(v_messages_791_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_789_);
lean_inc(v_ngen_788_);
lean_inc(v_nextMacroScope_787_);
lean_inc(v_env_786_);
lean_dec(v___x_785_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_805_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc(v_currNamespace_784_);
v___x_797_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_786_, v_ext_777_, v_b_778_, v_kind_779_, v_currNamespace_784_);
v___x_798_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 5, v___x_798_);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_nextMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_ngen_788_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_auxDeclNGen_789_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_traceState_790_);
lean_ctor_set(v_reuseFailAlloc_804_, 5, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 6, v_messages_791_);
lean_ctor_set(v_reuseFailAlloc_804_, 7, v_infoState_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 8, v_snapshotTasks_793_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_st_ref_put(v___y_781_, v___x_800_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_807_, lean_object* v_b_808_, lean_object* v_kind_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_kind_boxed_813_; lean_object* v_res_814_; 
v_kind_boxed_813_ = lean_unbox(v_kind_809_);
v_res_814_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_807_, v_b_808_, v_kind_boxed_813_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_00_u03c3_817_, lean_object* v_ext_818_, lean_object* v_b_819_, uint8_t v_kind_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_818_, v_b_819_, v_kind_820_, v___y_821_, v___y_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_00_u03c3_827_, lean_object* v_ext_828_, lean_object* v_b_829_, lean_object* v_kind_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v_kind_boxed_834_; lean_object* v_res_835_; 
v_kind_boxed_834_ = lean_unbox(v_kind_830_);
v_res_835_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_825_, v_00_u03b2_826_, v_00_u03c3_827_, v_ext_828_, v_b_829_, v_kind_boxed_834_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_836_, lean_object* v_declName_837_, uint8_t v_eager_838_, uint8_t v_attrKind_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
lean_inc(v_declName_837_);
v___x_843_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_837_, v_eager_838_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_844_, 0, v_declName_837_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v_eager_838_);
v___x_845_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_836_, v___x_844_, v_attrKind_839_, v_a_840_, v_a_841_);
return v___x_845_;
}
else
{
lean_dec(v_declName_837_);
lean_dec_ref(v_ext_836_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_846_, lean_object* v_declName_847_, lean_object* v_eager_848_, lean_object* v_attrKind_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_eager_boxed_853_; uint8_t v_attrKind_boxed_854_; lean_object* v_res_855_; 
v_eager_boxed_853_ = lean_unbox(v_eager_848_);
v_attrKind_boxed_854_ = lean_unbox(v_attrKind_849_);
v_res_855_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_846_, v_declName_847_, v_eager_boxed_853_, v_attrKind_boxed_854_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_856_, lean_object* v_declName_857_, uint8_t v_attrKind_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
lean_inc(v_declName_857_);
v___x_862_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_857_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_870_; 
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_862_, 0);
lean_dec(v_unused_871_);
v___x_864_ = v___x_862_;
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
else
{
lean_dec(v___x_862_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v_declName_857_);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_declName_857_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_856_, v___x_867_, v_attrKind_858_, v_a_859_, v_a_860_);
return v___x_868_;
}
}
}
else
{
lean_dec(v_declName_857_);
lean_dec_ref(v_ext_856_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_872_, lean_object* v_declName_873_, lean_object* v_attrKind_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
uint8_t v_attrKind_boxed_878_; lean_object* v_res_879_; 
v_attrKind_boxed_878_ = lean_unbox(v_attrKind_874_);
v_res_879_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_872_, v_declName_873_, v_attrKind_boxed_878_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_880_, lean_object* v_declName_881_, uint8_t v_attrKind_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_declName_881_);
v___x_887_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_880_, v___x_886_, v_attrKind_882_, v_a_883_, v_a_884_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_888_, lean_object* v_declName_889_, lean_object* v_attrKind_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_attrKind_boxed_894_; lean_object* v_res_895_; 
v_attrKind_boxed_894_ = lean_unbox(v_attrKind_890_);
v_res_895_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_888_, v_declName_889_, v_attrKind_boxed_894_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_896_, lean_object* v_s_897_){
_start:
{
lean_object* v_casesTypes_898_; lean_object* v_funCC_899_; lean_object* v_ematch_900_; lean_object* v_inj_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_casesTypes_898_ = lean_ctor_get(v_s_897_, 0);
v_funCC_899_ = lean_ctor_get(v_s_897_, 2);
v_ematch_900_ = lean_ctor_get(v_s_897_, 3);
v_inj_901_ = lean_ctor_get(v_s_897_, 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v_s_897_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_s_897_, 1);
lean_dec(v_unused_909_);
v___x_903_ = v_s_897_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_inj_901_);
lean_inc(v_ematch_900_);
lean_inc(v_funCC_899_);
lean_inc(v_casesTypes_898_);
lean_dec(v_s_897_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_a_896_);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_casesTypes_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_a_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_funCC_899_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_ematch_900_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_inj_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_910_, lean_object* v_declName_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v_ext_916_; lean_object* v_toEnvExtension_917_; lean_object* v_env_918_; lean_object* v_asyncMode_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_extThms_922_; lean_object* v___x_923_; 
v___x_915_ = lean_st_ref_get(v_a_913_);
v_ext_916_ = lean_ctor_get(v_ext_910_, 1);
v_toEnvExtension_917_ = lean_ctor_get(v_ext_916_, 0);
v_env_918_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_915_);
v_asyncMode_919_ = lean_ctor_get(v_toEnvExtension_917_, 2);
v___x_920_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_921_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_920_, v_ext_910_, v_env_918_, v_asyncMode_919_);
v_extThms_922_ = lean_ctor_get(v___x_921_, 1);
lean_inc_ref(v_extThms_922_);
lean_dec(v___x_921_);
v___x_923_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_922_, v_declName_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_953_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_953_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v_env_929_; lean_object* v_nextMacroScope_930_; lean_object* v_ngen_931_; lean_object* v_auxDeclNGen_932_; lean_object* v_traceState_933_; lean_object* v_messages_934_; lean_object* v_infoState_935_; lean_object* v_snapshotTasks_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_951_; 
v___x_928_ = lean_st_ref_take(v_a_913_);
v_env_929_ = lean_ctor_get(v___x_928_, 0);
v_nextMacroScope_930_ = lean_ctor_get(v___x_928_, 1);
v_ngen_931_ = lean_ctor_get(v___x_928_, 2);
v_auxDeclNGen_932_ = lean_ctor_get(v___x_928_, 3);
v_traceState_933_ = lean_ctor_get(v___x_928_, 4);
v_messages_934_ = lean_ctor_get(v___x_928_, 6);
v_infoState_935_ = lean_ctor_get(v___x_928_, 7);
v_snapshotTasks_936_ = lean_ctor_get(v___x_928_, 8);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_928_, 5);
lean_dec(v_unused_952_);
v___x_938_ = v___x_928_;
v_isShared_939_ = v_isSharedCheck_951_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snapshotTasks_936_);
lean_inc(v_infoState_935_);
lean_inc(v_messages_934_);
lean_inc(v_traceState_933_);
lean_inc(v_auxDeclNGen_932_);
lean_inc(v_ngen_931_);
lean_inc(v_nextMacroScope_930_);
lean_inc(v_env_929_);
lean_dec(v___x_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_951_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___f_940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_940_, 0, v_a_924_);
v___x_941_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_910_, v_env_929_, v___f_940_);
v___x_942_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 5, v___x_942_);
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_nextMacroScope_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_ngen_931_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_auxDeclNGen_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_traceState_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_messages_934_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_infoState_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_snapshotTasks_936_);
v___x_944_ = v_reuseFailAlloc_950_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = lean_st_ref_put(v_a_913_, v___x_944_);
v___x_946_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_946_);
v___x_948_ = v___x_926_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v_ext_910_);
v_a_954_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_923_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_923_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_962_, lean_object* v_declName_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_962_, v_declName_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_968_, lean_object* v_s_969_){
_start:
{
lean_object* v_extThms_970_; lean_object* v_funCC_971_; lean_object* v_ematch_972_; lean_object* v_inj_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_extThms_970_ = lean_ctor_get(v_s_969_, 1);
v_funCC_971_ = lean_ctor_get(v_s_969_, 2);
v_ematch_972_ = lean_ctor_get(v_s_969_, 3);
v_inj_973_ = lean_ctor_get(v_s_969_, 4);
v_isSharedCheck_980_ = !lean_is_exclusive(v_s_969_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_s_969_, 0);
lean_dec(v_unused_981_);
v___x_975_ = v_s_969_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_inj_973_);
lean_inc(v_ematch_972_);
lean_inc(v_funCC_971_);
lean_inc(v_extThms_970_);
lean_dec(v_s_969_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_a_968_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_968_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_extThms_970_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_funCC_971_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_ematch_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_inj_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_982_, lean_object* v_declName_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
lean_inc(v_declName_983_);
v___x_987_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; lean_object* v_ext_989_; lean_object* v_toEnvExtension_990_; lean_object* v_env_991_; lean_object* v_asyncMode_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_casesTypes_995_; lean_object* v___x_996_; 
lean_dec_ref_known(v___x_987_, 1);
v___x_988_ = lean_st_ref_get(v_a_985_);
v_ext_989_ = lean_ctor_get(v_ext_982_, 1);
v_toEnvExtension_990_ = lean_ctor_get(v_ext_989_, 0);
v_env_991_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_env_991_);
lean_dec(v___x_988_);
v_asyncMode_992_ = lean_ctor_get(v_toEnvExtension_990_, 2);
v___x_993_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_994_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_993_, v_ext_982_, v_env_991_, v_asyncMode_992_);
v_casesTypes_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_ref(v_casesTypes_995_);
lean_dec(v___x_994_);
v___x_996_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_995_, v_declName_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1026_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1026_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1026_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_env_1002_; lean_object* v_nextMacroScope_1003_; lean_object* v_ngen_1004_; lean_object* v_auxDeclNGen_1005_; lean_object* v_traceState_1006_; lean_object* v_messages_1007_; lean_object* v_infoState_1008_; lean_object* v_snapshotTasks_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1024_; 
v___x_1001_ = lean_st_ref_take(v_a_985_);
v_env_1002_ = lean_ctor_get(v___x_1001_, 0);
v_nextMacroScope_1003_ = lean_ctor_get(v___x_1001_, 1);
v_ngen_1004_ = lean_ctor_get(v___x_1001_, 2);
v_auxDeclNGen_1005_ = lean_ctor_get(v___x_1001_, 3);
v_traceState_1006_ = lean_ctor_get(v___x_1001_, 4);
v_messages_1007_ = lean_ctor_get(v___x_1001_, 6);
v_infoState_1008_ = lean_ctor_get(v___x_1001_, 7);
v_snapshotTasks_1009_ = lean_ctor_get(v___x_1001_, 8);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1001_, 5);
lean_dec(v_unused_1025_);
v___x_1011_ = v___x_1001_;
v_isShared_1012_ = v_isSharedCheck_1024_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snapshotTasks_1009_);
lean_inc(v_infoState_1008_);
lean_inc(v_messages_1007_);
lean_inc(v_traceState_1006_);
lean_inc(v_auxDeclNGen_1005_);
lean_inc(v_ngen_1004_);
lean_inc(v_nextMacroScope_1003_);
lean_inc(v_env_1002_);
lean_dec(v___x_1001_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1024_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___f_1013_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1013_, 0, v_a_997_);
v___x_1014_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_982_, v_env_1002_, v___f_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 5, v___x_1015_);
lean_ctor_set(v___x_1011_, 0, v___x_1014_);
v___x_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_nextMacroScope_1003_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_ngen_1004_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_auxDeclNGen_1005_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_traceState_1006_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_messages_1007_);
lean_ctor_set(v_reuseFailAlloc_1023_, 7, v_infoState_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 8, v_snapshotTasks_1009_);
v___x_1017_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_st_ref_put(v_a_985_, v___x_1017_);
v___x_1019_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1019_);
v___x_1021_ = v___x_999_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_ext_982_);
v_a_1027_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_996_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_996_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_dec(v_declName_983_);
lean_dec_ref(v_ext_982_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1035_, lean_object* v_declName_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1035_, v_declName_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1041_, lean_object* v_s_1042_){
_start:
{
lean_object* v_casesTypes_1043_; lean_object* v_extThms_1044_; lean_object* v_ematch_1045_; lean_object* v_inj_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_casesTypes_1043_ = lean_ctor_get(v_s_1042_, 0);
v_extThms_1044_ = lean_ctor_get(v_s_1042_, 1);
v_ematch_1045_ = lean_ctor_get(v_s_1042_, 3);
v_inj_1046_ = lean_ctor_get(v_s_1042_, 4);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_s_1042_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_s_1042_, 2);
lean_dec(v_unused_1054_);
v___x_1048_ = v_s_1042_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_inj_1046_);
lean_inc(v_ematch_1045_);
lean_inc(v_extThms_1044_);
lean_inc(v_casesTypes_1043_);
lean_dec(v_s_1042_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 2, v___x_1041_);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_casesTypes_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_extThms_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_ematch_1045_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_inj_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1055_, lean_object* v_t_1056_){
_start:
{
if (lean_obj_tag(v_t_1056_) == 0)
{
lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v_l_1059_; lean_object* v_r_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1714_; 
v_k_1057_ = lean_ctor_get(v_t_1056_, 1);
v_v_1058_ = lean_ctor_get(v_t_1056_, 2);
v_l_1059_ = lean_ctor_get(v_t_1056_, 3);
v_r_1060_ = lean_ctor_get(v_t_1056_, 4);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_t_1056_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_t_1056_, 0);
lean_dec(v_unused_1715_);
v___x_1062_ = v_t_1056_;
v_isShared_1063_ = v_isSharedCheck_1714_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_r_1060_);
lean_inc(v_l_1059_);
lean_inc(v_v_1058_);
lean_inc(v_k_1057_);
lean_dec(v_t_1056_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1714_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint8_t v___x_1064_; 
v___x_1064_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1055_, v_k_1057_);
switch(v___x_1064_)
{
case 0:
{
lean_object* v_impl_1065_; lean_object* v___x_1066_; 
v_impl_1065_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1055_, v_l_1059_);
v___x_1066_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1065_) == 0)
{
if (lean_obj_tag(v_r_1060_) == 0)
{
lean_object* v_size_1067_; lean_object* v_size_1068_; lean_object* v_k_1069_; lean_object* v_v_1070_; lean_object* v_l_1071_; lean_object* v_r_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_size_1067_ = lean_ctor_get(v_impl_1065_, 0);
lean_inc(v_size_1067_);
v_size_1068_ = lean_ctor_get(v_r_1060_, 0);
v_k_1069_ = lean_ctor_get(v_r_1060_, 1);
v_v_1070_ = lean_ctor_get(v_r_1060_, 2);
v_l_1071_ = lean_ctor_get(v_r_1060_, 3);
lean_inc(v_l_1071_);
v_r_1072_ = lean_ctor_get(v_r_1060_, 4);
v___x_1073_ = lean_unsigned_to_nat(3u);
v___x_1074_ = lean_nat_mul(v___x_1073_, v_size_1067_);
v___x_1075_ = lean_nat_dec_lt(v___x_1074_, v_size_1068_);
lean_dec(v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v_l_1071_);
v___x_1076_ = lean_nat_add(v___x_1066_, v_size_1067_);
lean_dec(v_size_1067_);
v___x_1077_ = lean_nat_add(v___x_1076_, v_size_1068_);
lean_dec(v___x_1076_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 3, v_impl_1065_);
lean_ctor_set(v___x_1062_, 0, v___x_1077_);
v___x_1079_ = v___x_1062_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_impl_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_r_1060_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
else
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1144_; 
lean_inc(v_r_1072_);
lean_inc(v_v_1070_);
lean_inc(v_k_1069_);
lean_inc(v_size_1068_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; lean_object* v_unused_1148_; lean_object* v_unused_1149_; 
v_unused_1145_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_r_1060_, 2);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_r_1060_, 1);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1149_);
v___x_1082_ = v_r_1060_;
v_isShared_1083_ = v_isSharedCheck_1144_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_r_1060_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1144_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_size_1084_; lean_object* v_k_1085_; lean_object* v_v_1086_; lean_object* v_l_1087_; lean_object* v_r_1088_; lean_object* v_size_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_size_1084_ = lean_ctor_get(v_l_1071_, 0);
v_k_1085_ = lean_ctor_get(v_l_1071_, 1);
v_v_1086_ = lean_ctor_get(v_l_1071_, 2);
v_l_1087_ = lean_ctor_get(v_l_1071_, 3);
v_r_1088_ = lean_ctor_get(v_l_1071_, 4);
v_size_1089_ = lean_ctor_get(v_r_1072_, 0);
v___x_1090_ = lean_unsigned_to_nat(2u);
v___x_1091_ = lean_nat_mul(v___x_1090_, v_size_1089_);
v___x_1092_ = lean_nat_dec_lt(v_size_1084_, v___x_1091_);
lean_dec(v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1120_; 
lean_inc(v_r_1088_);
lean_inc(v_l_1087_);
lean_inc(v_v_1086_);
lean_inc(v_k_1085_);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_l_1071_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; 
v_unused_1121_ = lean_ctor_get(v_l_1071_, 4);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_l_1071_, 3);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_l_1071_, 2);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v_l_1071_, 1);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_l_1071_, 0);
lean_dec(v_unused_1125_);
v___x_1094_ = v_l_1071_;
v_isShared_1095_ = v_isSharedCheck_1120_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v_l_1071_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1120_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1110_; 
v___x_1096_ = lean_nat_add(v___x_1066_, v_size_1067_);
lean_dec(v_size_1067_);
v___x_1097_ = lean_nat_add(v___x_1096_, v_size_1068_);
lean_dec(v_size_1068_);
if (lean_obj_tag(v_l_1087_) == 0)
{
lean_object* v_size_1118_; 
v_size_1118_ = lean_ctor_get(v_l_1087_, 0);
lean_inc(v_size_1118_);
v___y_1110_ = v_size_1118_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___y_1110_ = v___x_1119_;
goto v___jp_1109_;
}
v___jp_1098_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_nat_add(v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_r_1072_);
lean_ctor_set(v___x_1094_, 3, v_r_1088_);
lean_ctor_set(v___x_1094_, 2, v_v_1070_);
lean_ctor_set(v___x_1094_, 1, v_k_1069_);
lean_ctor_set(v___x_1094_, 0, v___x_1102_);
v___x_1104_ = v___x_1094_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_k_1069_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_v_1070_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_r_1088_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_r_1072_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 4, v___x_1104_);
lean_ctor_set(v___x_1082_, 3, v___y_1099_);
lean_ctor_set(v___x_1082_, 2, v_v_1086_);
lean_ctor_set(v___x_1082_, 1, v_k_1085_);
lean_ctor_set(v___x_1082_, 0, v___x_1097_);
v___x_1106_ = v___x_1082_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v___y_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_nat_add(v___x_1096_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec(v___x_1096_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_l_1087_);
lean_ctor_set(v___x_1062_, 3, v_impl_1065_);
lean_ctor_set(v___x_1062_, 0, v___x_1111_);
v___x_1113_ = v___x_1062_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_impl_1065_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_l_1087_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_nat_add(v___x_1066_, v_size_1089_);
if (lean_obj_tag(v_r_1088_) == 0)
{
lean_object* v_size_1115_; 
v_size_1115_ = lean_ctor_get(v_r_1088_, 0);
lean_inc(v_size_1115_);
v___y_1099_ = v___x_1113_;
v___y_1100_ = v___x_1114_;
v___y_1101_ = v_size_1115_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
v___y_1099_ = v___x_1113_;
v___y_1100_ = v___x_1114_;
v___y_1101_ = v___x_1116_;
goto v___jp_1098_;
}
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_del_object(v___x_1062_);
v___x_1126_ = lean_nat_add(v___x_1066_, v_size_1067_);
lean_dec(v_size_1067_);
v___x_1127_ = lean_nat_add(v___x_1126_, v_size_1068_);
lean_dec(v_size_1068_);
v___x_1128_ = lean_nat_add(v___x_1126_, v_size_1084_);
lean_dec(v___x_1126_);
lean_inc_ref(v_impl_1065_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 4, v_l_1071_);
lean_ctor_set(v___x_1082_, 3, v_impl_1065_);
lean_ctor_set(v___x_1082_, 2, v_v_1058_);
lean_ctor_set(v___x_1082_, 1, v_k_1057_);
lean_ctor_set(v___x_1082_, 0, v___x_1128_);
v___x_1130_ = v___x_1082_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_impl_1065_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_l_1071_);
v___x_1130_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v_impl_1065_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; lean_object* v_unused_1142_; 
v_unused_1138_ = lean_ctor_get(v_impl_1065_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_impl_1065_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_impl_1065_, 2);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_impl_1065_, 1);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_impl_1065_, 0);
lean_dec(v_unused_1142_);
v___x_1132_ = v_impl_1065_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v_impl_1065_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v_r_1072_);
lean_ctor_set(v___x_1132_, 3, v___x_1130_);
lean_ctor_set(v___x_1132_, 2, v_v_1070_);
lean_ctor_set(v___x_1132_, 1, v_k_1069_);
lean_ctor_set(v___x_1132_, 0, v___x_1127_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1069_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1070_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_r_1072_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v_size_1150_ = lean_ctor_get(v_impl_1065_, 0);
lean_inc(v_size_1150_);
v___x_1151_ = lean_nat_add(v___x_1066_, v_size_1150_);
lean_dec(v_size_1150_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 3, v_impl_1065_);
lean_ctor_set(v___x_1062_, 0, v___x_1151_);
v___x_1153_ = v___x_1062_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_impl_1065_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_r_1060_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
if (lean_obj_tag(v_r_1060_) == 0)
{
lean_object* v_l_1155_; 
v_l_1155_ = lean_ctor_get(v_r_1060_, 3);
lean_inc(v_l_1155_);
if (lean_obj_tag(v_l_1155_) == 0)
{
lean_object* v_r_1156_; 
v_r_1156_ = lean_ctor_get(v_r_1060_, 4);
lean_inc(v_r_1156_);
if (lean_obj_tag(v_r_1156_) == 0)
{
lean_object* v_size_1157_; lean_object* v_k_1158_; lean_object* v_v_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1172_; 
v_size_1157_ = lean_ctor_get(v_r_1060_, 0);
v_k_1158_ = lean_ctor_get(v_r_1060_, 1);
v_v_1159_ = lean_ctor_get(v_r_1060_, 2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1173_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1174_);
v___x_1161_ = v_r_1060_;
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_v_1159_);
lean_inc(v_k_1158_);
lean_inc(v_size_1157_);
lean_dec(v_r_1060_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_size_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v_size_1163_ = lean_ctor_get(v_l_1155_, 0);
v___x_1164_ = lean_nat_add(v___x_1066_, v_size_1157_);
lean_dec(v_size_1157_);
v___x_1165_ = lean_nat_add(v___x_1066_, v_size_1163_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 4, v_l_1155_);
lean_ctor_set(v___x_1161_, 3, v_impl_1065_);
lean_ctor_set(v___x_1161_, 2, v_v_1058_);
lean_ctor_set(v___x_1161_, 1, v_k_1057_);
lean_ctor_set(v___x_1161_, 0, v___x_1165_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_impl_1065_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_l_1155_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_r_1156_);
lean_ctor_set(v___x_1062_, 3, v___x_1167_);
lean_ctor_set(v___x_1062_, 2, v_v_1159_);
lean_ctor_set(v___x_1062_, 1, v_k_1158_);
lean_ctor_set(v___x_1062_, 0, v___x_1164_);
v___x_1169_ = v___x_1062_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1158_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1159_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_1156_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_k_1175_; lean_object* v_v_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1199_; 
v_k_1175_ = lean_ctor_get(v_r_1060_, 1);
v_v_1176_ = lean_ctor_get(v_r_1060_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; lean_object* v_unused_1201_; lean_object* v_unused_1202_; 
v_unused_1200_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1202_);
v___x_1178_ = v_r_1060_;
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_v_1176_);
lean_inc(v_k_1175_);
lean_dec(v_r_1060_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_k_1180_; lean_object* v_v_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1195_; 
v_k_1180_ = lean_ctor_get(v_l_1155_, 1);
v_v_1181_ = lean_ctor_get(v_l_1155_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_l_1155_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1196_ = lean_ctor_get(v_l_1155_, 4);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_l_1155_, 3);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_l_1155_, 0);
lean_dec(v_unused_1198_);
v___x_1183_ = v_l_1155_;
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_v_1181_);
lean_inc(v_k_1180_);
lean_dec(v_l_1155_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(3u);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 4, v_r_1156_);
lean_ctor_set(v___x_1183_, 3, v_r_1156_);
lean_ctor_set(v___x_1183_, 2, v_v_1058_);
lean_ctor_set(v___x_1183_, 1, v_k_1057_);
lean_ctor_set(v___x_1183_, 0, v___x_1066_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_r_1156_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_r_1156_);
v___x_1187_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 3, v_r_1156_);
lean_ctor_set(v___x_1178_, 0, v___x_1066_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_k_1175_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_v_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_r_1156_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_r_1156_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1189_);
lean_ctor_set(v___x_1062_, 3, v___x_1187_);
lean_ctor_set(v___x_1062_, 2, v_v_1181_);
lean_ctor_set(v___x_1062_, 1, v_k_1180_);
lean_ctor_set(v___x_1062_, 0, v___x_1185_);
v___x_1191_ = v___x_1062_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1181_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1203_; 
v_r_1203_ = lean_ctor_get(v_r_1060_, 4);
lean_inc(v_r_1203_);
if (lean_obj_tag(v_r_1203_) == 0)
{
lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1216_; 
v_k_1204_ = lean_ctor_get(v_r_1060_, 1);
v_v_1205_ = lean_ctor_get(v_r_1060_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; lean_object* v_unused_1218_; lean_object* v_unused_1219_; 
v_unused_1217_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1219_);
v___x_1207_ = v_r_1060_;
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_v_1205_);
lean_inc(v_k_1204_);
lean_dec(v_r_1060_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(3u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1155_);
lean_ctor_set(v___x_1207_, 2, v_v_1058_);
lean_ctor_set(v___x_1207_, 1, v_k_1057_);
lean_ctor_set(v___x_1207_, 0, v___x_1066_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_l_1155_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_r_1203_);
lean_ctor_set(v___x_1062_, 3, v___x_1211_);
lean_ctor_set(v___x_1062_, 2, v_v_1205_);
lean_ctor_set(v___x_1062_, 1, v_k_1204_);
lean_ctor_set(v___x_1062_, 0, v___x_1209_);
v___x_1213_ = v___x_1062_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1204_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1205_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_r_1203_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_size_1220_; lean_object* v_k_1221_; lean_object* v_v_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1233_; 
v_size_1220_ = lean_ctor_get(v_r_1060_, 0);
v_k_1221_ = lean_ctor_get(v_r_1060_, 1);
v_v_1222_ = lean_ctor_get(v_r_1060_, 2);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1234_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1235_);
v___x_1224_ = v_r_1060_;
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_v_1222_);
lean_inc(v_k_1221_);
lean_inc(v_size_1220_);
lean_dec(v_r_1060_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v_r_1203_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_size_1220_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1221_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_r_1203_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_r_1203_);
v___x_1227_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_unsigned_to_nat(2u);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1227_);
lean_ctor_set(v___x_1062_, 3, v_r_1203_);
lean_ctor_set(v___x_1062_, 0, v___x_1228_);
v___x_1230_ = v___x_1062_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_r_1203_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v___x_1227_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
else
{
lean_object* v___x_1237_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 3, v_r_1060_);
lean_ctor_set(v___x_1062_, 0, v___x_1066_);
v___x_1237_ = v___x_1062_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_r_1060_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_r_1060_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1062_);
lean_dec(v_v_1058_);
lean_dec(v_k_1057_);
if (lean_obj_tag(v_l_1059_) == 0)
{
if (lean_obj_tag(v_r_1060_) == 0)
{
lean_object* v_size_1239_; lean_object* v_k_1240_; lean_object* v_v_1241_; lean_object* v_l_1242_; lean_object* v_r_1243_; lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_size_1239_ = lean_ctor_get(v_l_1059_, 0);
v_k_1240_ = lean_ctor_get(v_l_1059_, 1);
v_v_1241_ = lean_ctor_get(v_l_1059_, 2);
v_l_1242_ = lean_ctor_get(v_l_1059_, 3);
v_r_1243_ = lean_ctor_get(v_l_1059_, 4);
lean_inc(v_r_1243_);
v_size_1244_ = lean_ctor_get(v_r_1060_, 0);
v_k_1245_ = lean_ctor_get(v_r_1060_, 1);
v_v_1246_ = lean_ctor_get(v_r_1060_, 2);
v_l_1247_ = lean_ctor_get(v_r_1060_, 3);
lean_inc(v_l_1247_);
v_r_1248_ = lean_ctor_get(v_r_1060_, 4);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_dec_lt(v_size_1239_, v_size_1244_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1386_; 
lean_inc(v_l_1242_);
lean_inc(v_v_1241_);
lean_inc(v_k_1240_);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; lean_object* v_unused_1388_; lean_object* v_unused_1389_; lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1387_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_l_1059_, 2);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_l_1059_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1391_);
v___x_1252_ = v_l_1059_;
v_isShared_1253_ = v_isSharedCheck_1386_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v_l_1059_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1386_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v_tree_1255_; 
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1240_, v_v_1241_, v_l_1242_, v_r_1243_);
v_tree_1255_ = lean_ctor_get(v___x_1254_, 2);
lean_inc(v_tree_1255_);
if (lean_obj_tag(v_tree_1255_) == 0)
{
lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_size_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_k_1256_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_k_1256_);
v_v_1257_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_v_1257_);
lean_dec_ref(v___x_1254_);
v_size_1258_ = lean_ctor_get(v_tree_1255_, 0);
v___x_1259_ = lean_unsigned_to_nat(3u);
v___x_1260_ = lean_nat_mul(v___x_1259_, v_size_1258_);
v___x_1261_ = lean_nat_dec_lt(v___x_1260_, v_size_1244_);
lean_dec(v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v_l_1247_);
v___x_1262_ = lean_nat_add(v___x_1249_, v_size_1258_);
v___x_1263_ = lean_nat_add(v___x_1262_, v_size_1244_);
lean_dec(v___x_1262_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1060_);
lean_ctor_set(v___x_1252_, 3, v_tree_1255_);
lean_ctor_set(v___x_1252_, 2, v_v_1257_);
lean_ctor_set(v___x_1252_, 1, v_k_1256_);
lean_ctor_set(v___x_1252_, 0, v___x_1263_);
v___x_1265_ = v___x_1252_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_tree_1255_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_r_1060_);
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
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1321_; 
lean_inc(v_r_1248_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
lean_inc(v_size_1244_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1322_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_r_1060_, 2);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_r_1060_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1326_);
v___x_1268_ = v_r_1060_;
v_isShared_1269_ = v_isSharedCheck_1321_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_r_1060_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1321_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_size_1270_; lean_object* v_k_1271_; lean_object* v_v_1272_; lean_object* v_l_1273_; lean_object* v_r_1274_; lean_object* v_size_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_size_1270_ = lean_ctor_get(v_l_1247_, 0);
v_k_1271_ = lean_ctor_get(v_l_1247_, 1);
v_v_1272_ = lean_ctor_get(v_l_1247_, 2);
v_l_1273_ = lean_ctor_get(v_l_1247_, 3);
v_r_1274_ = lean_ctor_get(v_l_1247_, 4);
v_size_1275_ = lean_ctor_get(v_r_1248_, 0);
v___x_1276_ = lean_unsigned_to_nat(2u);
v___x_1277_ = lean_nat_mul(v___x_1276_, v_size_1275_);
v___x_1278_ = lean_nat_dec_lt(v_size_1270_, v___x_1277_);
lean_dec(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1306_; 
lean_inc(v_r_1274_);
lean_inc(v_l_1273_);
lean_inc(v_v_1272_);
lean_inc(v_k_1271_);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_l_1247_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; lean_object* v_unused_1308_; lean_object* v_unused_1309_; lean_object* v_unused_1310_; lean_object* v_unused_1311_; 
v_unused_1307_ = lean_ctor_get(v_l_1247_, 4);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_l_1247_, 3);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_l_1247_, 2);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v_l_1247_, 1);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v_l_1247_, 0);
lean_dec(v_unused_1311_);
v___x_1280_ = v_l_1247_;
v_isShared_1281_ = v_isSharedCheck_1306_;
goto v_resetjp_1279_;
}
else
{
lean_dec(v_l_1247_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1306_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1296_; 
v___x_1282_ = lean_nat_add(v___x_1249_, v_size_1258_);
v___x_1283_ = lean_nat_add(v___x_1282_, v_size_1244_);
lean_dec(v_size_1244_);
if (lean_obj_tag(v_l_1273_) == 0)
{
lean_object* v_size_1304_; 
v_size_1304_ = lean_ctor_get(v_l_1273_, 0);
lean_inc(v_size_1304_);
v___y_1296_ = v_size_1304_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___y_1296_ = v___x_1305_;
goto v___jp_1295_;
}
v___jp_1284_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_nat_add(v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v_r_1248_);
lean_ctor_set(v___x_1280_, 3, v_r_1274_);
lean_ctor_set(v___x_1280_, 2, v_v_1246_);
lean_ctor_set(v___x_1280_, 1, v_k_1245_);
lean_ctor_set(v___x_1280_, 0, v___x_1288_);
v___x_1290_ = v___x_1280_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_r_1274_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_r_1248_);
v___x_1290_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___x_1290_);
lean_ctor_set(v___x_1268_, 3, v___y_1285_);
lean_ctor_set(v___x_1268_, 2, v_v_1272_);
lean_ctor_set(v___x_1268_, 1, v_k_1271_);
lean_ctor_set(v___x_1268_, 0, v___x_1283_);
v___x_1292_ = v___x_1268_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1271_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1272_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v___y_1285_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
v___jp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_nat_add(v___x_1282_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec(v___x_1282_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_l_1273_);
lean_ctor_set(v___x_1252_, 3, v_tree_1255_);
lean_ctor_set(v___x_1252_, 2, v_v_1257_);
lean_ctor_set(v___x_1252_, 1, v_k_1256_);
lean_ctor_set(v___x_1252_, 0, v___x_1297_);
v___x_1299_ = v___x_1252_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_tree_1255_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_l_1273_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_nat_add(v___x_1249_, v_size_1275_);
if (lean_obj_tag(v_r_1274_) == 0)
{
lean_object* v_size_1301_; 
v_size_1301_ = lean_ctor_get(v_r_1274_, 0);
lean_inc(v_size_1301_);
v___y_1285_ = v___x_1299_;
v___y_1286_ = v___x_1300_;
v___y_1287_ = v_size_1301_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___y_1285_ = v___x_1299_;
v___y_1286_ = v___x_1300_;
v___y_1287_ = v___x_1302_;
goto v___jp_1284_;
}
}
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1312_ = lean_nat_add(v___x_1249_, v_size_1258_);
v___x_1313_ = lean_nat_add(v___x_1312_, v_size_1244_);
lean_dec(v_size_1244_);
v___x_1314_ = lean_nat_add(v___x_1312_, v_size_1270_);
lean_dec(v___x_1312_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_l_1247_);
lean_ctor_set(v___x_1268_, 3, v_tree_1255_);
lean_ctor_set(v___x_1268_, 2, v_v_1257_);
lean_ctor_set(v___x_1268_, 1, v_k_1256_);
lean_ctor_set(v___x_1268_, 0, v___x_1314_);
v___x_1316_ = v___x_1268_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_tree_1255_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_l_1247_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1248_);
lean_ctor_set(v___x_1252_, 3, v___x_1316_);
lean_ctor_set(v___x_1252_, 2, v_v_1246_);
lean_ctor_set(v___x_1252_, 1, v_k_1245_);
lean_ctor_set(v___x_1252_, 0, v___x_1313_);
v___x_1318_ = v___x_1252_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_r_1248_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
else
{
lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1380_; 
lean_inc(v_r_1248_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
lean_inc(v_size_1244_);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; lean_object* v_unused_1385_; 
v_unused_1381_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_r_1060_, 2);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_r_1060_, 1);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1385_);
v___x_1328_ = v_r_1060_;
v_isShared_1329_ = v_isSharedCheck_1380_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v_r_1060_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1380_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
if (lean_obj_tag(v_l_1247_) == 0)
{
if (lean_obj_tag(v_r_1248_) == 0)
{
lean_object* v_k_1330_; lean_object* v_v_1331_; lean_object* v_size_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_k_1330_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_k_1330_);
v_v_1331_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_v_1331_);
lean_dec_ref(v___x_1254_);
v_size_1332_ = lean_ctor_get(v_l_1247_, 0);
v___x_1333_ = lean_nat_add(v___x_1249_, v_size_1244_);
lean_dec(v_size_1244_);
v___x_1334_ = lean_nat_add(v___x_1249_, v_size_1332_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v_l_1247_);
lean_ctor_set(v___x_1328_, 3, v_tree_1255_);
lean_ctor_set(v___x_1328_, 2, v_v_1331_);
lean_ctor_set(v___x_1328_, 1, v_k_1330_);
lean_ctor_set(v___x_1328_, 0, v___x_1334_);
v___x_1336_ = v___x_1328_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1330_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1331_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_tree_1255_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_l_1247_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1248_);
lean_ctor_set(v___x_1252_, 3, v___x_1336_);
lean_ctor_set(v___x_1252_, 2, v_v_1246_);
lean_ctor_set(v___x_1252_, 1, v_k_1245_);
lean_ctor_set(v___x_1252_, 0, v___x_1333_);
v___x_1338_ = v___x_1252_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1248_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v_k_1343_; lean_object* v_v_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_size_1244_);
v_k_1341_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_k_1341_);
v_v_1342_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_v_1342_);
lean_dec_ref(v___x_1254_);
v_k_1343_ = lean_ctor_get(v_l_1247_, 1);
v_v_1344_ = lean_ctor_get(v_l_1247_, 2);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_l_1247_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; 
v_unused_1359_ = lean_ctor_get(v_l_1247_, 4);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_l_1247_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_l_1247_, 0);
lean_dec(v_unused_1361_);
v___x_1346_ = v_l_1247_;
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_v_1344_);
lean_inc(v_k_1343_);
lean_dec(v_l_1247_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(3u);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v_r_1248_);
lean_ctor_set(v___x_1346_, 3, v_r_1248_);
lean_ctor_set(v___x_1346_, 2, v_v_1342_);
lean_ctor_set(v___x_1346_, 1, v_k_1341_);
lean_ctor_set(v___x_1346_, 0, v___x_1249_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_r_1248_);
v___x_1350_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 3, v_r_1248_);
lean_ctor_set(v___x_1328_, 0, v___x_1249_);
v___x_1352_ = v___x_1328_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1248_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v___x_1352_);
lean_ctor_set(v___x_1252_, 3, v___x_1350_);
lean_ctor_set(v___x_1252_, 2, v_v_1344_);
lean_ctor_set(v___x_1252_, 1, v_k_1343_);
lean_ctor_set(v___x_1252_, 0, v___x_1348_);
v___x_1354_ = v___x_1252_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1248_) == 0)
{
lean_object* v_k_1362_; lean_object* v_v_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v_size_1244_);
v_k_1362_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_k_1362_);
v_v_1363_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_v_1363_);
lean_dec_ref(v___x_1254_);
v___x_1364_ = lean_unsigned_to_nat(3u);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v_l_1247_);
lean_ctor_set(v___x_1328_, 2, v_v_1363_);
lean_ctor_set(v___x_1328_, 1, v_k_1362_);
lean_ctor_set(v___x_1328_, 0, v___x_1249_);
v___x_1366_ = v___x_1328_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_k_1362_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_v_1363_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_l_1247_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_l_1247_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v_r_1248_);
lean_ctor_set(v___x_1252_, 3, v___x_1366_);
lean_ctor_set(v___x_1252_, 2, v_v_1246_);
lean_ctor_set(v___x_1252_, 1, v_k_1245_);
lean_ctor_set(v___x_1252_, 0, v___x_1364_);
v___x_1368_ = v___x_1252_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_r_1248_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v___x_1374_; 
v_k_1371_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_k_1371_);
v_v_1372_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_v_1372_);
lean_dec_ref(v___x_1254_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 3, v_r_1248_);
v___x_1374_ = v___x_1328_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_size_1244_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_r_1248_);
v___x_1374_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(2u);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 4, v___x_1374_);
lean_ctor_set(v___x_1252_, 3, v_r_1248_);
lean_ctor_set(v___x_1252_, 2, v_v_1372_);
lean_ctor_set(v___x_1252_, 1, v_k_1371_);
lean_ctor_set(v___x_1252_, 0, v___x_1375_);
v___x_1377_ = v___x_1252_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v___x_1374_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
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
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1544_; 
lean_inc(v_r_1248_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_r_1060_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1545_ = lean_ctor_get(v_r_1060_, 4);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_r_1060_, 3);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_r_1060_, 2);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_r_1060_, 1);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1060_, 0);
lean_dec(v_unused_1549_);
v___x_1393_ = v_r_1060_;
v_isShared_1394_ = v_isSharedCheck_1544_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_r_1060_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1544_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v_tree_1396_; 
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1245_, v_v_1246_, v_l_1247_, v_r_1248_);
v_tree_1396_ = lean_ctor_get(v___x_1395_, 2);
lean_inc(v_tree_1396_);
if (lean_obj_tag(v_tree_1396_) == 0)
{
lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_size_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_k_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_k_1397_);
v_v_1398_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_v_1398_);
lean_dec_ref(v___x_1395_);
v_size_1399_ = lean_ctor_get(v_tree_1396_, 0);
v___x_1400_ = lean_unsigned_to_nat(3u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1399_);
v___x_1402_ = lean_nat_dec_lt(v___x_1401_, v_size_1239_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_dec(v_r_1243_);
v___x_1403_ = lean_nat_add(v___x_1249_, v_size_1239_);
v___x_1404_ = lean_nat_add(v___x_1403_, v_size_1399_);
lean_dec(v___x_1403_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_tree_1396_);
lean_ctor_set(v___x_1393_, 3, v_l_1059_);
lean_ctor_set(v___x_1393_, 2, v_v_1398_);
lean_ctor_set(v___x_1393_, 1, v_k_1397_);
lean_ctor_set(v___x_1393_, 0, v___x_1404_);
v___x_1406_ = v___x_1393_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_tree_1396_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1473_; 
lean_inc(v_l_1242_);
lean_inc(v_v_1241_);
lean_inc(v_k_1240_);
lean_inc(v_size_1239_);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1474_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_l_1059_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_l_1059_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1478_);
v___x_1409_ = v_l_1059_;
v_isShared_1410_ = v_isSharedCheck_1473_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_l_1059_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1473_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_size_1411_; lean_object* v_size_1412_; lean_object* v_k_1413_; lean_object* v_v_1414_; lean_object* v_l_1415_; lean_object* v_r_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_size_1411_ = lean_ctor_get(v_l_1242_, 0);
v_size_1412_ = lean_ctor_get(v_r_1243_, 0);
v_k_1413_ = lean_ctor_get(v_r_1243_, 1);
v_v_1414_ = lean_ctor_get(v_r_1243_, 2);
v_l_1415_ = lean_ctor_get(v_r_1243_, 3);
v_r_1416_ = lean_ctor_get(v_r_1243_, 4);
v___x_1417_ = lean_unsigned_to_nat(2u);
v___x_1418_ = lean_nat_mul(v___x_1417_, v_size_1411_);
v___x_1419_ = lean_nat_dec_lt(v_size_1412_, v___x_1418_);
lean_dec(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1457_; 
lean_inc(v_r_1416_);
lean_inc(v_l_1415_);
lean_inc(v_v_1414_);
lean_inc(v_k_1413_);
lean_del_object(v___x_1409_);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_r_1243_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; 
v_unused_1458_ = lean_ctor_get(v_r_1243_, 4);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_r_1243_, 3);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1243_, 2);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_r_1243_, 1);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_r_1243_, 0);
lean_dec(v_unused_1462_);
v___x_1421_ = v_r_1243_;
v_isShared_1422_ = v_isSharedCheck_1457_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_r_1243_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1457_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1445_; lean_object* v___y_1447_; 
v___x_1423_ = lean_nat_add(v___x_1249_, v_size_1239_);
lean_dec(v_size_1239_);
v___x_1424_ = lean_nat_add(v___x_1423_, v_size_1399_);
lean_dec(v___x_1423_);
v___x_1445_ = lean_nat_add(v___x_1249_, v_size_1411_);
if (lean_obj_tag(v_l_1415_) == 0)
{
lean_object* v_size_1455_; 
v_size_1455_ = lean_ctor_get(v_l_1415_, 0);
lean_inc(v_size_1455_);
v___y_1447_ = v_size_1455_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___y_1447_ = v___x_1456_;
goto v___jp_1446_;
}
v___jp_1425_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_nat_add(v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
lean_inc_ref(v_tree_1396_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v_tree_1396_);
lean_ctor_set(v___x_1421_, 3, v_r_1416_);
lean_ctor_set(v___x_1421_, 2, v_v_1398_);
lean_ctor_set(v___x_1421_, 1, v_k_1397_);
lean_ctor_set(v___x_1421_, 0, v___x_1429_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_r_1416_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_tree_1396_);
v___x_1431_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_isSharedCheck_1438_ = !lean_is_exclusive(v_tree_1396_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1439_ = lean_ctor_get(v_tree_1396_, 4);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_tree_1396_, 3);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_tree_1396_, 2);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_tree_1396_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_tree_1396_, 0);
lean_dec(v_unused_1443_);
v___x_1433_ = v_tree_1396_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v_tree_1396_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v___x_1431_);
lean_ctor_set(v___x_1433_, 3, v___y_1426_);
lean_ctor_set(v___x_1433_, 2, v_v_1414_);
lean_ctor_set(v___x_1433_, 1, v_k_1413_);
lean_ctor_set(v___x_1433_, 0, v___x_1424_);
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___y_1426_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
v___jp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_nat_add(v___x_1445_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec(v___x_1445_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1415_);
lean_ctor_set(v___x_1393_, 3, v_l_1242_);
lean_ctor_set(v___x_1393_, 2, v_v_1241_);
lean_ctor_set(v___x_1393_, 1, v_k_1240_);
lean_ctor_set(v___x_1393_, 0, v___x_1448_);
v___x_1450_ = v___x_1393_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1240_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1241_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_l_1415_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_nat_add(v___x_1249_, v_size_1399_);
if (lean_obj_tag(v_r_1416_) == 0)
{
lean_object* v_size_1452_; 
v_size_1452_ = lean_ctor_get(v_r_1416_, 0);
lean_inc(v_size_1452_);
v___y_1426_ = v___x_1450_;
v___y_1427_ = v___x_1451_;
v___y_1428_ = v_size_1452_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___y_1426_ = v___x_1450_;
v___y_1427_ = v___x_1451_;
v___y_1428_ = v___x_1453_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1463_ = lean_nat_add(v___x_1249_, v_size_1239_);
lean_dec(v_size_1239_);
v___x_1464_ = lean_nat_add(v___x_1463_, v_size_1399_);
lean_dec(v___x_1463_);
v___x_1465_ = lean_nat_add(v___x_1249_, v_size_1399_);
v___x_1466_ = lean_nat_add(v___x_1465_, v_size_1412_);
lean_dec(v___x_1465_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_tree_1396_);
lean_ctor_set(v___x_1393_, 3, v_r_1243_);
lean_ctor_set(v___x_1393_, 2, v_v_1398_);
lean_ctor_set(v___x_1393_, 1, v_k_1397_);
lean_ctor_set(v___x_1393_, 0, v___x_1466_);
v___x_1468_ = v___x_1393_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_r_1243_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_tree_1396_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1468_);
lean_ctor_set(v___x_1409_, 0, v___x_1464_);
v___x_1470_ = v___x_1409_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_k_1240_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_v_1241_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1242_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1502_; 
lean_inc_ref(v_l_1242_);
lean_inc(v_v_1241_);
lean_inc(v_k_1240_);
lean_inc(v_size_1239_);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1503_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1059_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_l_1059_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1507_);
v___x_1480_ = v_l_1059_;
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_l_1059_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
if (lean_obj_tag(v_r_1243_) == 0)
{
lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v_size_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v_k_1482_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_k_1482_);
v_v_1483_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_v_1483_);
lean_dec_ref(v___x_1395_);
v_size_1484_ = lean_ctor_get(v_r_1243_, 0);
v___x_1485_ = lean_nat_add(v___x_1249_, v_size_1239_);
lean_dec(v_size_1239_);
v___x_1486_ = lean_nat_add(v___x_1249_, v_size_1484_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_tree_1396_);
lean_ctor_set(v___x_1393_, 3, v_r_1243_);
lean_ctor_set(v___x_1393_, 2, v_v_1483_);
lean_ctor_set(v___x_1393_, 1, v_k_1482_);
lean_ctor_set(v___x_1393_, 0, v___x_1486_);
v___x_1488_ = v___x_1393_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1482_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1483_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_r_1243_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_tree_1396_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v___x_1488_);
lean_ctor_set(v___x_1480_, 0, v___x_1485_);
v___x_1490_ = v___x_1480_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1240_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1241_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v_k_1493_; lean_object* v_v_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec(v_size_1239_);
v_k_1493_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_k_1493_);
v_v_1494_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_v_1494_);
lean_dec_ref(v___x_1395_);
v___x_1495_ = lean_unsigned_to_nat(3u);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_r_1243_);
lean_ctor_set(v___x_1393_, 3, v_r_1243_);
lean_ctor_set(v___x_1393_, 2, v_v_1494_);
lean_ctor_set(v___x_1393_, 1, v_k_1493_);
lean_ctor_set(v___x_1393_, 0, v___x_1249_);
v___x_1497_ = v___x_1393_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1493_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1494_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_r_1243_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1243_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v___x_1497_);
lean_ctor_set(v___x_1480_, 0, v___x_1495_);
v___x_1499_ = v___x_1480_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1240_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1241_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v___x_1497_);
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
else
{
if (lean_obj_tag(v_r_1243_) == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1532_; 
lean_inc(v_l_1242_);
lean_inc(v_v_1241_);
lean_inc(v_k_1240_);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; 
v_unused_1533_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1059_, 2);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1059_, 1);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1537_);
v___x_1509_ = v_l_1059_;
v_isShared_1510_ = v_isSharedCheck_1532_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_l_1059_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1532_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_k_1513_; lean_object* v_v_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1528_; 
v_k_1511_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_k_1511_);
v_v_1512_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_v_1512_);
lean_dec_ref(v___x_1395_);
v_k_1513_ = lean_ctor_get(v_r_1243_, 1);
v_v_1514_ = lean_ctor_get(v_r_1243_, 2);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_r_1243_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; 
v_unused_1529_ = lean_ctor_get(v_r_1243_, 4);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_r_1243_, 3);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_r_1243_, 0);
lean_dec(v_unused_1531_);
v___x_1516_ = v_r_1243_;
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_v_1514_);
lean_inc(v_k_1513_);
lean_dec(v_r_1243_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_unsigned_to_nat(3u);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 4, v_l_1242_);
lean_ctor_set(v___x_1516_, 3, v_l_1242_);
lean_ctor_set(v___x_1516_, 2, v_v_1241_);
lean_ctor_set(v___x_1516_, 1, v_k_1240_);
lean_ctor_set(v___x_1516_, 0, v___x_1249_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1240_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1241_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v_l_1242_);
v___x_1520_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_l_1242_);
lean_ctor_set(v___x_1393_, 3, v_l_1242_);
lean_ctor_set(v___x_1393_, 2, v_v_1512_);
lean_ctor_set(v___x_1393_, 1, v_k_1511_);
lean_ctor_set(v___x_1393_, 0, v___x_1249_);
v___x_1522_ = v___x_1393_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_l_1242_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_l_1242_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v___x_1522_);
lean_ctor_set(v___x_1509_, 3, v___x_1520_);
lean_ctor_set(v___x_1509_, 2, v_v_1514_);
lean_ctor_set(v___x_1509_, 1, v_k_1513_);
lean_ctor_set(v___x_1509_, 0, v___x_1518_);
v___x_1524_ = v___x_1509_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
else
{
lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v_k_1538_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_k_1538_);
v_v_1539_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_v_1539_);
lean_dec_ref(v___x_1395_);
v___x_1540_ = lean_unsigned_to_nat(2u);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 4, v_r_1243_);
lean_ctor_set(v___x_1393_, 3, v_l_1059_);
lean_ctor_set(v___x_1393_, 2, v_v_1539_);
lean_ctor_set(v___x_1393_, 1, v_k_1538_);
lean_ctor_set(v___x_1393_, 0, v___x_1540_);
v___x_1542_ = v___x_1393_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_r_1243_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
}
else
{
return v_l_1059_;
}
}
else
{
return v_r_1060_;
}
}
default: 
{
lean_object* v_impl_1550_; lean_object* v___x_1551_; 
v_impl_1550_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1055_, v_r_1060_);
v___x_1551_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1550_) == 0)
{
if (lean_obj_tag(v_l_1059_) == 0)
{
lean_object* v_size_1552_; lean_object* v_size_1553_; lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v_l_1556_; lean_object* v_r_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_size_1552_ = lean_ctor_get(v_impl_1550_, 0);
lean_inc(v_size_1552_);
v_size_1553_ = lean_ctor_get(v_l_1059_, 0);
v_k_1554_ = lean_ctor_get(v_l_1059_, 1);
v_v_1555_ = lean_ctor_get(v_l_1059_, 2);
v_l_1556_ = lean_ctor_get(v_l_1059_, 3);
v_r_1557_ = lean_ctor_get(v_l_1059_, 4);
lean_inc(v_r_1557_);
v___x_1558_ = lean_unsigned_to_nat(3u);
v___x_1559_ = lean_nat_mul(v___x_1558_, v_size_1552_);
v___x_1560_ = lean_nat_dec_lt(v___x_1559_, v_size_1553_);
lean_dec(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
lean_dec(v_r_1557_);
v___x_1561_ = lean_nat_add(v___x_1551_, v_size_1553_);
v___x_1562_ = lean_nat_add(v___x_1561_, v_size_1552_);
lean_dec(v_size_1552_);
lean_dec(v___x_1561_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_impl_1550_);
lean_ctor_set(v___x_1062_, 0, v___x_1562_);
v___x_1564_ = v___x_1062_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_impl_1550_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1631_; 
lean_inc(v_l_1556_);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
lean_inc(v_size_1553_);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1632_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_l_1059_, 2);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_l_1059_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1636_);
v___x_1567_ = v_l_1059_;
v_isShared_1568_ = v_isSharedCheck_1631_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_l_1059_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1631_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_size_1569_; lean_object* v_size_1570_; lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v_l_1573_; lean_object* v_r_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_size_1569_ = lean_ctor_get(v_l_1556_, 0);
v_size_1570_ = lean_ctor_get(v_r_1557_, 0);
v_k_1571_ = lean_ctor_get(v_r_1557_, 1);
v_v_1572_ = lean_ctor_get(v_r_1557_, 2);
v_l_1573_ = lean_ctor_get(v_r_1557_, 3);
v_r_1574_ = lean_ctor_get(v_r_1557_, 4);
v___x_1575_ = lean_unsigned_to_nat(2u);
v___x_1576_ = lean_nat_mul(v___x_1575_, v_size_1569_);
v___x_1577_ = lean_nat_dec_lt(v_size_1570_, v___x_1576_);
lean_dec(v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1606_; 
lean_inc(v_r_1574_);
lean_inc(v_l_1573_);
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_r_1557_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1607_ = lean_ctor_get(v_r_1557_, 4);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1557_, 3);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_r_1557_, 2);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1557_, 1);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_r_1557_, 0);
lean_dec(v_unused_1611_);
v___x_1579_ = v_r_1557_;
v_isShared_1580_ = v_isSharedCheck_1606_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v_r_1557_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1606_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___x_1594_; lean_object* v___y_1596_; 
v___x_1581_ = lean_nat_add(v___x_1551_, v_size_1553_);
lean_dec(v_size_1553_);
v___x_1582_ = lean_nat_add(v___x_1581_, v_size_1552_);
lean_dec(v___x_1581_);
v___x_1594_ = lean_nat_add(v___x_1551_, v_size_1569_);
if (lean_obj_tag(v_l_1573_) == 0)
{
lean_object* v_size_1604_; 
v_size_1604_ = lean_ctor_get(v_l_1573_, 0);
lean_inc(v_size_1604_);
v___y_1596_ = v_size_1604_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___y_1596_ = v___x_1605_;
goto v___jp_1595_;
}
v___jp_1583_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = lean_nat_add(v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_impl_1550_);
lean_ctor_set(v___x_1579_, 3, v_r_1574_);
lean_ctor_set(v___x_1579_, 2, v_v_1058_);
lean_ctor_set(v___x_1579_, 1, v_k_1057_);
lean_ctor_set(v___x_1579_, 0, v___x_1587_);
v___x_1589_ = v___x_1579_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_r_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_impl_1550_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v___x_1589_);
lean_ctor_set(v___x_1567_, 3, v___y_1584_);
lean_ctor_set(v___x_1567_, 2, v_v_1572_);
lean_ctor_set(v___x_1567_, 1, v_k_1571_);
lean_ctor_set(v___x_1567_, 0, v___x_1582_);
v___x_1591_ = v___x_1567_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v___y_1584_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_nat_add(v___x_1594_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec(v___x_1594_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_l_1573_);
lean_ctor_set(v___x_1062_, 3, v_l_1556_);
lean_ctor_set(v___x_1062_, 2, v_v_1555_);
lean_ctor_set(v___x_1062_, 1, v_k_1554_);
lean_ctor_set(v___x_1062_, 0, v___x_1597_);
v___x_1599_ = v___x_1062_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_l_1573_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_nat_add(v___x_1551_, v_size_1552_);
lean_dec(v_size_1552_);
if (lean_obj_tag(v_r_1574_) == 0)
{
lean_object* v_size_1601_; 
v_size_1601_ = lean_ctor_get(v_r_1574_, 0);
lean_inc(v_size_1601_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v___x_1600_;
v___y_1586_ = v_size_1601_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_unsigned_to_nat(0u);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v___x_1600_;
v___y_1586_ = v___x_1602_;
goto v___jp_1583_;
}
}
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_del_object(v___x_1062_);
v___x_1612_ = lean_nat_add(v___x_1551_, v_size_1553_);
lean_dec(v_size_1553_);
v___x_1613_ = lean_nat_add(v___x_1612_, v_size_1552_);
lean_dec(v___x_1612_);
v___x_1614_ = lean_nat_add(v___x_1551_, v_size_1552_);
lean_dec(v_size_1552_);
v___x_1615_ = lean_nat_add(v___x_1614_, v_size_1570_);
lean_dec(v___x_1614_);
lean_inc_ref(v_impl_1550_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_impl_1550_);
lean_ctor_set(v___x_1567_, 3, v_r_1557_);
lean_ctor_set(v___x_1567_, 2, v_v_1058_);
lean_ctor_set(v___x_1567_, 1, v_k_1057_);
lean_ctor_set(v___x_1567_, 0, v___x_1615_);
v___x_1617_ = v___x_1567_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_r_1557_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_impl_1550_);
v___x_1617_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_isSharedCheck_1624_ = !lean_is_exclusive(v_impl_1550_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; lean_object* v_unused_1628_; lean_object* v_unused_1629_; 
v_unused_1625_ = lean_ctor_get(v_impl_1550_, 4);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_impl_1550_, 3);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_impl_1550_, 2);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_impl_1550_, 1);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_impl_1550_, 0);
lean_dec(v_unused_1629_);
v___x_1619_ = v_impl_1550_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_impl_1550_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___x_1617_);
lean_ctor_set(v___x_1619_, 3, v_l_1556_);
lean_ctor_set(v___x_1619_, 2, v_v_1555_);
lean_ctor_set(v___x_1619_, 1, v_k_1554_);
lean_ctor_set(v___x_1619_, 0, v___x_1613_);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v___x_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
v_size_1637_ = lean_ctor_get(v_impl_1550_, 0);
lean_inc(v_size_1637_);
v___x_1638_ = lean_nat_add(v___x_1551_, v_size_1637_);
lean_dec(v_size_1637_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_impl_1550_);
lean_ctor_set(v___x_1062_, 0, v___x_1638_);
v___x_1640_ = v___x_1062_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_impl_1550_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
if (lean_obj_tag(v_l_1059_) == 0)
{
lean_object* v_l_1642_; 
v_l_1642_ = lean_ctor_get(v_l_1059_, 3);
if (lean_obj_tag(v_l_1642_) == 0)
{
lean_object* v_r_1643_; 
lean_inc_ref(v_l_1642_);
v_r_1643_ = lean_ctor_get(v_l_1059_, 4);
lean_inc(v_r_1643_);
if (lean_obj_tag(v_r_1643_) == 0)
{
lean_object* v_size_1644_; lean_object* v_k_1645_; lean_object* v_v_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1659_; 
v_size_1644_ = lean_ctor_get(v_l_1059_, 0);
v_k_1645_ = lean_ctor_get(v_l_1059_, 1);
v_v_1646_ = lean_ctor_get(v_l_1059_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; 
v_unused_1660_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1661_);
v___x_1648_ = v_l_1059_;
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_v_1646_);
lean_inc(v_k_1645_);
lean_inc(v_size_1644_);
lean_dec(v_l_1059_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v_size_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v_size_1650_ = lean_ctor_get(v_r_1643_, 0);
v___x_1651_ = lean_nat_add(v___x_1551_, v_size_1644_);
lean_dec(v_size_1644_);
v___x_1652_ = lean_nat_add(v___x_1551_, v_size_1650_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v_impl_1550_);
lean_ctor_set(v___x_1648_, 3, v_r_1643_);
lean_ctor_set(v___x_1648_, 2, v_v_1058_);
lean_ctor_set(v___x_1648_, 1, v_k_1057_);
lean_ctor_set(v___x_1648_, 0, v___x_1652_);
v___x_1654_ = v___x_1648_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_r_1643_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_impl_1550_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1654_);
lean_ctor_set(v___x_1062_, 3, v_l_1642_);
lean_ctor_set(v___x_1062_, 2, v_v_1646_);
lean_ctor_set(v___x_1062_, 1, v_k_1645_);
lean_ctor_set(v___x_1062_, 0, v___x_1651_);
v___x_1656_ = v___x_1062_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_l_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1674_; 
v_k_1662_ = lean_ctor_get(v_l_1059_, 1);
v_v_1663_ = lean_ctor_get(v_l_1059_, 2);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1675_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1677_);
v___x_1665_ = v_l_1059_;
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_v_1663_);
lean_inc(v_k_1662_);
lean_dec(v_l_1059_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = lean_unsigned_to_nat(3u);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 3, v_r_1643_);
lean_ctor_set(v___x_1665_, 2, v_v_1058_);
lean_ctor_set(v___x_1665_, 1, v_k_1057_);
lean_ctor_set(v___x_1665_, 0, v___x_1551_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_r_1643_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_r_1643_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1669_);
lean_ctor_set(v___x_1062_, 3, v_l_1642_);
lean_ctor_set(v___x_1062_, 2, v_v_1663_);
lean_ctor_set(v___x_1062_, 1, v_k_1662_);
lean_ctor_set(v___x_1062_, 0, v___x_1667_);
v___x_1671_ = v___x_1062_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_l_1642_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
else
{
lean_object* v_r_1678_; 
v_r_1678_ = lean_ctor_get(v_l_1059_, 4);
lean_inc(v_r_1678_);
if (lean_obj_tag(v_r_1678_) == 0)
{
lean_object* v_k_1679_; lean_object* v_v_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_l_1642_);
v_k_1679_ = lean_ctor_get(v_l_1059_, 1);
v_v_1680_ = lean_ctor_get(v_l_1059_, 2);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_l_1059_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1704_ = lean_ctor_get(v_l_1059_, 4);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1059_, 3);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1059_, 0);
lean_dec(v_unused_1706_);
v___x_1682_ = v_l_1059_;
v_isShared_1683_ = v_isSharedCheck_1703_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_v_1680_);
lean_inc(v_k_1679_);
lean_dec(v_l_1059_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1703_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_k_1684_; lean_object* v_v_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1699_; 
v_k_1684_ = lean_ctor_get(v_r_1678_, 1);
v_v_1685_ = lean_ctor_get(v_r_1678_, 2);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_r_1678_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1700_ = lean_ctor_get(v_r_1678_, 4);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_r_1678_, 3);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_r_1678_, 0);
lean_dec(v_unused_1702_);
v___x_1687_ = v_r_1678_;
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_v_1685_);
lean_inc(v_k_1684_);
lean_dec(v_r_1678_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_unsigned_to_nat(3u);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 4, v_l_1642_);
lean_ctor_set(v___x_1687_, 3, v_l_1642_);
lean_ctor_set(v___x_1687_, 2, v_v_1680_);
lean_ctor_set(v___x_1687_, 1, v_k_1679_);
lean_ctor_set(v___x_1687_, 0, v___x_1551_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_k_1679_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_v_1680_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_l_1642_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_l_1642_);
v___x_1691_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 4, v_l_1642_);
lean_ctor_set(v___x_1682_, 2, v_v_1058_);
lean_ctor_set(v___x_1682_, 1, v_k_1057_);
lean_ctor_set(v___x_1682_, 0, v___x_1551_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_l_1642_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_l_1642_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___x_1693_);
lean_ctor_set(v___x_1062_, 3, v___x_1691_);
lean_ctor_set(v___x_1062_, 2, v_v_1685_);
lean_ctor_set(v___x_1062_, 1, v_k_1684_);
lean_ctor_set(v___x_1062_, 0, v___x_1689_);
v___x_1695_ = v___x_1062_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_k_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_v_1685_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_unsigned_to_nat(2u);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_r_1678_);
lean_ctor_set(v___x_1062_, 0, v___x_1707_);
v___x_1709_ = v___x_1062_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_r_1678_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v___x_1712_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_l_1059_);
lean_ctor_set(v___x_1062_, 0, v___x_1551_);
v___x_1712_ = v___x_1062_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_l_1059_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
}
else
{
return v_t_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1716_, lean_object* v_t_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1716_, v_t_1717_);
lean_dec(v_k_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1719_, lean_object* v_declName_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_ext_1725_; lean_object* v_toEnvExtension_1726_; lean_object* v_env_1727_; lean_object* v_asyncMode_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___y_1732_; lean_object* v_funCC_1758_; uint8_t v___x_1759_; 
v___x_1724_ = lean_st_ref_get(v_a_1722_);
v_ext_1725_ = lean_ctor_get(v_ext_1719_, 1);
v_toEnvExtension_1726_ = lean_ctor_get(v_ext_1725_, 0);
v_env_1727_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_env_1727_);
lean_dec(v___x_1724_);
v_asyncMode_1728_ = lean_ctor_get(v_toEnvExtension_1726_, 2);
v___x_1729_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1730_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1729_, v_ext_1719_, v_env_1727_, v_asyncMode_1728_);
v_funCC_1758_ = lean_ctor_get(v___x_1730_, 2);
lean_inc(v_funCC_1758_);
v___x_1759_ = l_Lean_NameSet_contains(v_funCC_1758_, v_declName_1720_);
lean_dec(v_funCC_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc(v_declName_1720_);
v___x_1760_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1720_, v_a_1721_, v_a_1722_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec_ref_known(v___x_1760_, 1);
v___y_1732_ = v_a_1722_;
goto v___jp_1731_;
}
else
{
lean_dec(v___x_1730_);
lean_dec(v_declName_1720_);
lean_dec_ref(v_ext_1719_);
return v___x_1760_;
}
}
else
{
v___y_1732_ = v_a_1722_;
goto v___jp_1731_;
}
v___jp_1731_:
{
lean_object* v_funCC_1733_; lean_object* v___x_1734_; lean_object* v_env_1735_; lean_object* v_nextMacroScope_1736_; lean_object* v_ngen_1737_; lean_object* v_auxDeclNGen_1738_; lean_object* v_traceState_1739_; lean_object* v_messages_1740_; lean_object* v_infoState_1741_; lean_object* v_snapshotTasks_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1756_; 
v_funCC_1733_ = lean_ctor_get(v___x_1730_, 2);
lean_inc(v_funCC_1733_);
lean_dec(v___x_1730_);
v___x_1734_ = lean_st_ref_take(v___y_1732_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
v_nextMacroScope_1736_ = lean_ctor_get(v___x_1734_, 1);
v_ngen_1737_ = lean_ctor_get(v___x_1734_, 2);
v_auxDeclNGen_1738_ = lean_ctor_get(v___x_1734_, 3);
v_traceState_1739_ = lean_ctor_get(v___x_1734_, 4);
v_messages_1740_ = lean_ctor_get(v___x_1734_, 6);
v_infoState_1741_ = lean_ctor_get(v___x_1734_, 7);
v_snapshotTasks_1742_ = lean_ctor_get(v___x_1734_, 8);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1734_, 5);
lean_dec(v_unused_1757_);
v___x_1744_ = v___x_1734_;
v_isShared_1745_ = v_isSharedCheck_1756_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snapshotTasks_1742_);
lean_inc(v_infoState_1741_);
lean_inc(v_messages_1740_);
lean_inc(v_traceState_1739_);
lean_inc(v_auxDeclNGen_1738_);
lean_inc(v_ngen_1737_);
lean_inc(v_nextMacroScope_1736_);
lean_inc(v_env_1735_);
lean_dec(v___x_1734_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1756_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1720_, v_funCC_1733_);
lean_dec(v_declName_1720_);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1747_, 0, v___x_1746_);
v___x_1748_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1719_, v_env_1735_, v___f_1747_);
v___x_1749_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 5, v___x_1749_);
lean_ctor_set(v___x_1744_, 0, v___x_1748_);
v___x_1751_ = v___x_1744_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_nextMacroScope_1736_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_ngen_1737_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_auxDeclNGen_1738_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_traceState_1739_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v_messages_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_infoState_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_snapshotTasks_1742_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_st_ref_put(v___y_1732_, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1761_, lean_object* v_declName_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1761_, v_declName_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1767_, lean_object* v_k_1768_, lean_object* v_t_1769_, lean_object* v_h_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1768_, v_t_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1772_, lean_object* v_k_1773_, lean_object* v_t_1774_, lean_object* v_h_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1772_, v_k_1773_, v_t_1774_, v_h_1775_);
lean_dec(v_k_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1777_, lean_object* v_s_1778_){
_start:
{
lean_object* v_casesTypes_1779_; lean_object* v_extThms_1780_; lean_object* v_funCC_1781_; lean_object* v_inj_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_casesTypes_1779_ = lean_ctor_get(v_s_1778_, 0);
v_extThms_1780_ = lean_ctor_get(v_s_1778_, 1);
v_funCC_1781_ = lean_ctor_get(v_s_1778_, 2);
v_inj_1782_ = lean_ctor_get(v_s_1778_, 4);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_s_1778_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_s_1778_, 3);
lean_dec(v_unused_1790_);
v___x_1784_ = v_s_1778_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_inj_1782_);
lean_inc(v_funCC_1781_);
lean_inc(v_extThms_1780_);
lean_inc(v_casesTypes_1779_);
lean_dec(v_s_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 3, v_a_1777_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_casesTypes_1779_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_extThms_1780_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_funCC_1781_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_inj_1782_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
lean_ctor_set(v___x_1792_, 3, v___x_1791_);
lean_ctor_set(v___x_1792_, 4, v___x_1791_);
lean_ctor_set(v___x_1792_, 5, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1793_, lean_object* v_declName_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v_ext_1801_; lean_object* v_toEnvExtension_1802_; lean_object* v_env_1803_; lean_object* v_asyncMode_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_ematch_1807_; lean_object* v___x_1808_; 
v___x_1800_ = lean_st_ref_get(v_a_1798_);
v_ext_1801_ = lean_ctor_get(v_ext_1793_, 1);
v_toEnvExtension_1802_ = lean_ctor_get(v_ext_1801_, 0);
v_env_1803_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_env_1803_);
lean_dec(v___x_1800_);
v_asyncMode_1804_ = lean_ctor_get(v_toEnvExtension_1802_, 2);
v___x_1805_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1806_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1805_, v_ext_1793_, v_env_1803_, v_asyncMode_1804_);
v_ematch_1807_ = lean_ctor_get(v___x_1806_, 3);
lean_inc_ref(v_ematch_1807_);
lean_dec(v___x_1806_);
v___x_1808_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1807_, v_declName_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1853_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1853_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1853_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v_env_1814_; lean_object* v_nextMacroScope_1815_; lean_object* v_ngen_1816_; lean_object* v_auxDeclNGen_1817_; lean_object* v_traceState_1818_; lean_object* v_messages_1819_; lean_object* v_infoState_1820_; lean_object* v_snapshotTasks_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1851_; 
v___x_1813_ = lean_st_ref_take(v_a_1798_);
v_env_1814_ = lean_ctor_get(v___x_1813_, 0);
v_nextMacroScope_1815_ = lean_ctor_get(v___x_1813_, 1);
v_ngen_1816_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1817_ = lean_ctor_get(v___x_1813_, 3);
v_traceState_1818_ = lean_ctor_get(v___x_1813_, 4);
v_messages_1819_ = lean_ctor_get(v___x_1813_, 6);
v_infoState_1820_ = lean_ctor_get(v___x_1813_, 7);
v_snapshotTasks_1821_ = lean_ctor_get(v___x_1813_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1813_, 5);
lean_dec(v_unused_1852_);
v___x_1823_ = v___x_1813_;
v_isShared_1824_ = v_isSharedCheck_1851_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snapshotTasks_1821_);
lean_inc(v_infoState_1820_);
lean_inc(v_messages_1819_);
lean_inc(v_traceState_1818_);
lean_inc(v_auxDeclNGen_1817_);
lean_inc(v_ngen_1816_);
lean_inc(v_nextMacroScope_1815_);
lean_inc(v_env_1814_);
lean_dec(v___x_1813_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1851_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___f_1825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1825_, 0, v_a_1809_);
v___x_1826_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1793_, v_env_1814_, v___f_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 5, v___x_1827_);
lean_ctor_set(v___x_1823_, 0, v___x_1826_);
v___x_1829_ = v___x_1823_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_nextMacroScope_1815_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ngen_1816_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_auxDeclNGen_1817_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_traceState_1818_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_messages_1819_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v_infoState_1820_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_snapshotTasks_1821_);
v___x_1829_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v_mctx_1832_; lean_object* v_zetaDeltaFVarIds_1833_; lean_object* v_postponed_1834_; lean_object* v_diag_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1848_; 
v___x_1830_ = lean_st_ref_put(v_a_1798_, v___x_1829_);
v___x_1831_ = lean_st_ref_take(v_a_1796_);
v_mctx_1832_ = lean_ctor_get(v___x_1831_, 0);
v_zetaDeltaFVarIds_1833_ = lean_ctor_get(v___x_1831_, 2);
v_postponed_1834_ = lean_ctor_get(v___x_1831_, 3);
v_diag_1835_ = lean_ctor_get(v___x_1831_, 4);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1831_, 1);
lean_dec(v_unused_1849_);
v___x_1837_ = v___x_1831_;
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_diag_1835_);
lean_inc(v_postponed_1834_);
lean_inc(v_zetaDeltaFVarIds_1833_);
lean_inc(v_mctx_1832_);
lean_dec(v___x_1831_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 1, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_mctx_1832_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_zetaDeltaFVarIds_1833_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_postponed_1834_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_diag_1835_);
v___x_1841_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1842_ = lean_st_ref_put(v_a_1796_, v___x_1841_);
v___x_1843_ = lean_box(0);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1843_);
v___x_1845_ = v___x_1811_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_ext_1793_);
v_a_1854_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1808_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1808_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1862_, lean_object* v_declName_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1862_, v_declName_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1870_, lean_object* v_s_1871_){
_start:
{
lean_object* v_casesTypes_1872_; lean_object* v_extThms_1873_; lean_object* v_funCC_1874_; lean_object* v_ematch_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_casesTypes_1872_ = lean_ctor_get(v_s_1871_, 0);
v_extThms_1873_ = lean_ctor_get(v_s_1871_, 1);
v_funCC_1874_ = lean_ctor_get(v_s_1871_, 2);
v_ematch_1875_ = lean_ctor_get(v_s_1871_, 3);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_s_1871_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v_s_1871_, 4);
lean_dec(v_unused_1883_);
v___x_1877_ = v_s_1871_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_ematch_1875_);
lean_inc(v_funCC_1874_);
lean_inc(v_extThms_1873_);
lean_inc(v_casesTypes_1872_);
lean_dec(v_s_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v_a_1870_);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_casesTypes_1872_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_extThms_1873_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_funCC_1874_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_ematch_1875_);
lean_ctor_set(v_reuseFailAlloc_1881_, 4, v_a_1870_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1884_, lean_object* v_declName_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v_ext_1892_; lean_object* v_toEnvExtension_1893_; lean_object* v_env_1894_; lean_object* v_asyncMode_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_inj_1898_; lean_object* v___x_1899_; 
v___x_1891_ = lean_st_ref_get(v_a_1889_);
v_ext_1892_ = lean_ctor_get(v_ext_1884_, 1);
v_toEnvExtension_1893_ = lean_ctor_get(v_ext_1892_, 0);
v_env_1894_ = lean_ctor_get(v___x_1891_, 0);
lean_inc_ref(v_env_1894_);
lean_dec(v___x_1891_);
v_asyncMode_1895_ = lean_ctor_get(v_toEnvExtension_1893_, 2);
v___x_1896_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1897_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1896_, v_ext_1884_, v_env_1894_, v_asyncMode_1895_);
v_inj_1898_ = lean_ctor_get(v___x_1897_, 4);
lean_inc_ref(v_inj_1898_);
lean_dec(v___x_1897_);
v___x_1899_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1898_, v_declName_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1944_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1944_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1944_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v_env_1905_; lean_object* v_nextMacroScope_1906_; lean_object* v_ngen_1907_; lean_object* v_auxDeclNGen_1908_; lean_object* v_traceState_1909_; lean_object* v_messages_1910_; lean_object* v_infoState_1911_; lean_object* v_snapshotTasks_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1942_; 
v___x_1904_ = lean_st_ref_take(v_a_1889_);
v_env_1905_ = lean_ctor_get(v___x_1904_, 0);
v_nextMacroScope_1906_ = lean_ctor_get(v___x_1904_, 1);
v_ngen_1907_ = lean_ctor_get(v___x_1904_, 2);
v_auxDeclNGen_1908_ = lean_ctor_get(v___x_1904_, 3);
v_traceState_1909_ = lean_ctor_get(v___x_1904_, 4);
v_messages_1910_ = lean_ctor_get(v___x_1904_, 6);
v_infoState_1911_ = lean_ctor_get(v___x_1904_, 7);
v_snapshotTasks_1912_ = lean_ctor_get(v___x_1904_, 8);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v___x_1904_, 5);
lean_dec(v_unused_1943_);
v___x_1914_ = v___x_1904_;
v_isShared_1915_ = v_isSharedCheck_1942_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snapshotTasks_1912_);
lean_inc(v_infoState_1911_);
lean_inc(v_messages_1910_);
lean_inc(v_traceState_1909_);
lean_inc(v_auxDeclNGen_1908_);
lean_inc(v_ngen_1907_);
lean_inc(v_nextMacroScope_1906_);
lean_inc(v_env_1905_);
lean_dec(v___x_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1942_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___f_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1916_, 0, v_a_1900_);
v___x_1917_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1884_, v_env_1905_, v___f_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 5, v___x_1918_);
lean_ctor_set(v___x_1914_, 0, v___x_1917_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_nextMacroScope_1906_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_ngen_1907_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_auxDeclNGen_1908_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_traceState_1909_);
lean_ctor_set(v_reuseFailAlloc_1941_, 5, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1941_, 6, v_messages_1910_);
lean_ctor_set(v_reuseFailAlloc_1941_, 7, v_infoState_1911_);
lean_ctor_set(v_reuseFailAlloc_1941_, 8, v_snapshotTasks_1912_);
v___x_1920_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_mctx_1923_; lean_object* v_zetaDeltaFVarIds_1924_; lean_object* v_postponed_1925_; lean_object* v_diag_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1939_; 
v___x_1921_ = lean_st_ref_put(v_a_1889_, v___x_1920_);
v___x_1922_ = lean_st_ref_take(v_a_1887_);
v_mctx_1923_ = lean_ctor_get(v___x_1922_, 0);
v_zetaDeltaFVarIds_1924_ = lean_ctor_get(v___x_1922_, 2);
v_postponed_1925_ = lean_ctor_get(v___x_1922_, 3);
v_diag_1926_ = lean_ctor_get(v___x_1922_, 4);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1922_, 1);
lean_dec(v_unused_1940_);
v___x_1928_ = v___x_1922_;
v_isShared_1929_ = v_isSharedCheck_1939_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_diag_1926_);
lean_inc(v_postponed_1925_);
lean_inc(v_zetaDeltaFVarIds_1924_);
lean_inc(v_mctx_1923_);
lean_dec(v___x_1922_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1939_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_mctx_1923_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_zetaDeltaFVarIds_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_postponed_1925_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_diag_1926_);
v___x_1932_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1933_ = lean_st_ref_put(v_a_1887_, v___x_1932_);
v___x_1934_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1934_);
v___x_1936_ = v___x_1902_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_ext_1884_);
v_a_1945_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1899_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1899_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1953_, lean_object* v_declName_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1953_, v_declName_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1961_, lean_object* v_i_1962_, lean_object* v_k_1963_){
_start:
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = lean_array_get_size(v_keys_1961_);
v___x_1965_ = lean_nat_dec_lt(v_i_1962_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_dec(v_i_1962_);
return v___x_1965_;
}
else
{
lean_object* v_k_x27_1966_; uint8_t v___x_1967_; 
v_k_x27_1966_ = lean_array_fget_borrowed(v_keys_1961_, v_i_1962_);
v___x_1967_ = lean_name_eq(v_k_1963_, v_k_x27_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_nat_add(v_i_1962_, v___x_1968_);
lean_dec(v_i_1962_);
v_i_1962_ = v___x_1969_;
goto _start;
}
else
{
lean_dec(v_i_1962_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1971_, lean_object* v_i_1972_, lean_object* v_k_1973_){
_start:
{
uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_res_1974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1971_, v_i_1972_, v_k_1973_);
lean_dec(v_k_1973_);
lean_dec_ref(v_keys_1971_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1976_, size_t v_x_1977_, lean_object* v_x_1978_){
_start:
{
if (lean_obj_tag(v_x_1976_) == 0)
{
lean_object* v_es_1979_; lean_object* v___x_1980_; size_t v___x_1981_; size_t v___x_1982_; lean_object* v_j_1983_; lean_object* v___x_1984_; 
v_es_1979_ = lean_ctor_get(v_x_1976_, 0);
v___x_1980_ = lean_box(2);
v___x_1981_ = ((size_t)31ULL);
v___x_1982_ = lean_usize_land(v_x_1977_, v___x_1981_);
v_j_1983_ = lean_usize_to_nat(v___x_1982_);
v___x_1984_ = lean_array_get_borrowed(v___x_1980_, v_es_1979_, v_j_1983_);
lean_dec(v_j_1983_);
switch(lean_obj_tag(v___x_1984_))
{
case 0:
{
lean_object* v_key_1985_; uint8_t v___x_1986_; 
v_key_1985_ = lean_ctor_get(v___x_1984_, 0);
v___x_1986_ = lean_name_eq(v_x_1978_, v_key_1985_);
return v___x_1986_;
}
case 1:
{
lean_object* v_node_1987_; size_t v___x_1988_; size_t v___x_1989_; 
v_node_1987_ = lean_ctor_get(v___x_1984_, 0);
v___x_1988_ = ((size_t)5ULL);
v___x_1989_ = lean_usize_shift_right(v_x_1977_, v___x_1988_);
v_x_1976_ = v_node_1987_;
v_x_1977_ = v___x_1989_;
goto _start;
}
default: 
{
uint8_t v___x_1991_; 
v___x_1991_ = 0;
return v___x_1991_;
}
}
}
else
{
lean_object* v_ks_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_ks_1992_ = lean_ctor_get(v_x_1976_, 0);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1992_, v___x_1993_, v_x_1978_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
size_t v_x_326__boxed_1998_; uint8_t v_res_1999_; lean_object* v_r_2000_; 
v_x_326__boxed_1998_ = lean_unbox_usize(v_x_1996_);
lean_dec(v_x_1996_);
v_res_1999_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1995_, v_x_326__boxed_1998_, v_x_1997_);
lean_dec(v_x_1997_);
lean_dec_ref(v_x_1995_);
v_r_2000_ = lean_box(v_res_1999_);
return v_r_2000_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
uint64_t v___y_2004_; 
if (lean_obj_tag(v_x_2002_) == 0)
{
uint64_t v___x_2007_; 
v___x_2007_ = 1723ULL;
v___y_2004_ = v___x_2007_;
goto v___jp_2003_;
}
else
{
uint64_t v_hash_2008_; 
v_hash_2008_ = lean_ctor_get_uint64(v_x_2002_, sizeof(void*)*2);
v___y_2004_ = v_hash_2008_;
goto v___jp_2003_;
}
v___jp_2003_:
{
size_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = lean_uint64_to_usize(v___y_2004_);
v___x_2006_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2001_, v___x_2005_, v_x_2002_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
uint8_t v_res_2011_; lean_object* v_r_2012_; 
v_res_2011_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2009_, v_x_2010_);
lean_dec(v_x_2010_);
lean_dec_ref(v_x_2009_);
v_r_2012_ = lean_box(v_res_2011_);
return v_r_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2013_, lean_object* v_declName_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v_ext_2018_; lean_object* v_toEnvExtension_2019_; lean_object* v_env_2020_; lean_object* v_asyncMode_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v_extThms_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2017_ = lean_st_ref_get(v_a_2015_);
v_ext_2018_ = lean_ctor_get(v_ext_2013_, 1);
v_toEnvExtension_2019_ = lean_ctor_get(v_ext_2018_, 0);
v_env_2020_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_env_2020_);
lean_dec(v___x_2017_);
v_asyncMode_2021_ = lean_ctor_get(v_toEnvExtension_2019_, 2);
v___x_2022_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2023_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2022_, v_ext_2013_, v_env_2020_, v_asyncMode_2021_);
v_extThms_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc_ref(v_extThms_2024_);
lean_dec(v___x_2023_);
v___x_2025_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2024_, v_declName_2014_);
lean_dec_ref(v_extThms_2024_);
v___x_2026_ = lean_box(v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2028_, lean_object* v_declName_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2028_, v_declName_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec(v_declName_2029_);
lean_dec_ref(v_ext_2028_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2033_, lean_object* v_declName_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2033_, v_declName_2034_, v_a_2036_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2039_, lean_object* v_declName_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2039_, v_declName_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_declName_2040_);
lean_dec_ref(v_ext_2039_);
return v_res_2044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2046_, v_x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
uint8_t v_res_2052_; lean_object* v_r_2053_; 
v_res_2052_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2049_, v_x_2050_, v_x_2051_);
lean_dec(v_x_2051_);
lean_dec_ref(v_x_2050_);
v_r_2053_ = lean_box(v_res_2052_);
return v_r_2053_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2054_, lean_object* v_x_2055_, size_t v_x_2056_, lean_object* v_x_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2055_, v_x_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
size_t v_x_411__boxed_2063_; uint8_t v_res_2064_; lean_object* v_r_2065_; 
v_x_411__boxed_2063_ = lean_unbox_usize(v_x_2061_);
lean_dec(v_x_2061_);
v_res_2064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2059_, v_x_2060_, v_x_411__boxed_2063_, v_x_2062_);
lean_dec(v_x_2062_);
lean_dec_ref(v_x_2060_);
v_r_2065_ = lean_box(v_res_2064_);
return v_r_2065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2066_, lean_object* v_keys_2067_, lean_object* v_vals_2068_, lean_object* v_heq_2069_, lean_object* v_i_2070_, lean_object* v_k_2071_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2067_, v_i_2070_, v_k_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2073_, lean_object* v_keys_2074_, lean_object* v_vals_2075_, lean_object* v_heq_2076_, lean_object* v_i_2077_, lean_object* v_k_2078_){
_start:
{
uint8_t v_res_2079_; lean_object* v_r_2080_; 
v_res_2079_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2073_, v_keys_2074_, v_vals_2075_, v_heq_2076_, v_i_2077_, v_k_2078_);
lean_dec(v_k_2078_);
lean_dec_ref(v_vals_2075_);
lean_dec_ref(v_keys_2074_);
v_r_2080_ = lean_box(v_res_2079_);
return v_r_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2081_, lean_object* v_declName_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v_ext_2086_; lean_object* v_toEnvExtension_2087_; lean_object* v_env_2088_; lean_object* v_asyncMode_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_inj_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2085_ = lean_st_ref_get(v_a_2083_);
v_ext_2086_ = lean_ctor_get(v_ext_2081_, 1);
v_toEnvExtension_2087_ = lean_ctor_get(v_ext_2086_, 0);
v_env_2088_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_ref(v_env_2088_);
lean_dec(v___x_2085_);
v_asyncMode_2089_ = lean_ctor_get(v_toEnvExtension_2087_, 2);
v___x_2090_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2091_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2090_, v_ext_2081_, v_env_2088_, v_asyncMode_2089_);
v_inj_2092_ = lean_ctor_get(v___x_2091_, 4);
lean_inc_ref(v_inj_2092_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_declName_2082_);
v___x_2094_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2092_, v___x_2093_);
lean_dec_ref_known(v___x_2093_, 1);
lean_dec_ref(v_inj_2092_);
v___x_2095_ = lean_box(v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2097_, lean_object* v_declName_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2097_, v_declName_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_ext_2097_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2102_, lean_object* v_declName_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2102_, v_declName_2103_, v_a_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2108_, lean_object* v_declName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2108_, v_declName_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec_ref(v_ext_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2114_, lean_object* v_declName_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_ext_2119_; lean_object* v_toEnvExtension_2120_; lean_object* v_env_2121_; lean_object* v_asyncMode_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_funCC_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2118_ = lean_st_ref_get(v_a_2116_);
v_ext_2119_ = lean_ctor_get(v_ext_2114_, 1);
v_toEnvExtension_2120_ = lean_ctor_get(v_ext_2119_, 0);
v_env_2121_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_env_2121_);
lean_dec(v___x_2118_);
v_asyncMode_2122_ = lean_ctor_get(v_toEnvExtension_2120_, 2);
v___x_2123_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2124_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2123_, v_ext_2114_, v_env_2121_, v_asyncMode_2122_);
v_funCC_2125_ = lean_ctor_get(v___x_2124_, 2);
lean_inc(v_funCC_2125_);
lean_dec(v___x_2124_);
v___x_2126_ = l_Lean_NameSet_contains(v_funCC_2125_, v_declName_2115_);
lean_dec(v_funCC_2125_);
v___x_2127_ = lean_box(v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2129_, lean_object* v_declName_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2129_, v_declName_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec(v_declName_2130_);
lean_dec_ref(v_ext_2129_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2134_, lean_object* v_declName_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2134_, v_declName_2135_, v_a_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2140_, lean_object* v_declName_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2140_, v_declName_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_declName_2141_);
lean_dec_ref(v_ext_2140_);
return v_res_2145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2170_ = l_Lean_mkAtom(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2173_ = lean_array_push(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2183_ = l_Lean_mkAtom(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2186_ = lean_array_push(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2189_ = lean_box(2);
v___x_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
lean_ctor_set(v___x_2190_, 2, v___x_2187_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2196_ = lean_box(2);
v___x_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
lean_ctor_set(v___x_2197_, 2, v___x_2194_);
return v___x_2197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2203_ = lean_box(2);
v___x_2204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2202_);
lean_ctor_set(v___x_2204_, 2, v___x_2201_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2207_ = lean_array_push(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2210_ = lean_box(2);
v___x_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v___x_2208_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2217_ = lean_box(2);
v___x_2218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2216_);
lean_ctor_set(v___x_2218_, 2, v___x_2215_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2220_, lean_object* v_ext_2221_, lean_object* v_____r_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = 0;
lean_inc(v_declName_2220_);
v___x_2229_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2220_, v___x_2228_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; uint8_t v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v_a_2233_; uint8_t v___x_2234_; 
v___x_2232_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2221_, v_declName_2220_, v___y_2226_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = lean_unbox(v_a_2233_);
lean_dec(v_a_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v_a_2236_; uint8_t v___x_2237_; 
lean_inc(v_declName_2220_);
v___x_2235_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2221_, v_declName_2220_, v___y_2226_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v_a_2239_; uint8_t v___x_2240_; 
v___x_2238_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2221_, v_declName_2220_, v___y_2226_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_unbox(v_a_2239_);
lean_dec(v_a_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2221_, v_declName_2220_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; 
v___x_2242_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2221_, v_declName_2220_, v___y_2225_, v___y_2226_);
return v___x_2242_;
}
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2221_, v_declName_2220_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2243_;
}
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2221_, v_declName_2220_, v___y_2225_, v___y_2226_);
return v___x_2244_;
}
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2221_, v_declName_2220_, v___y_2225_, v___y_2226_);
return v___x_2245_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_ext_2221_);
lean_dec(v_declName_2220_);
v_a_2246_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2229_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2229_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2254_, lean_object* v_ext_2255_, lean_object* v_____r_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2254_, v_ext_2255_, v_____r_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; lean_object* v_env_2270_; lean_object* v___x_2271_; lean_object* v_toCold_2272_; lean_object* v_mctx_2273_; lean_object* v_lctx_2274_; lean_object* v_options_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2269_ = lean_st_ref_get(v___y_2267_);
v_env_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc_ref(v_env_2270_);
lean_dec(v___x_2269_);
v___x_2271_ = lean_st_ref_get(v___y_2265_);
v_toCold_2272_ = lean_ctor_get(v___y_2266_, 0);
v_mctx_2273_ = lean_ctor_get(v___x_2271_, 0);
lean_inc_ref(v_mctx_2273_);
lean_dec(v___x_2271_);
v_lctx_2274_ = lean_ctor_get(v___y_2264_, 2);
v_options_2275_ = lean_ctor_get(v_toCold_2272_, 2);
lean_inc_ref(v_options_2275_);
lean_inc_ref(v_lctx_2274_);
v___x_2276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2276_, 0, v_env_2270_);
lean_ctor_set(v___x_2276_, 1, v_mctx_2273_);
lean_ctor_set(v___x_2276_, 2, v_lctx_2274_);
lean_ctor_set(v___x_2276_, 3, v_options_2275_);
v___x_2277_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_msgData_2263_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_ref_2292_; lean_object* v___x_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_ref_2292_ = lean_ctor_get(v___y_2289_, 2);
v___x_2293_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_inc(v_ref_2292_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_ref_2292_);
lean_ctor_set(v___x_2298_, 1, v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 1);
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2309_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2316_; uint64_t v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2320_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set_uint64(v___x_2320_, sizeof(void*)*1, v___x_2318_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_box(1);
v___x_2325_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2326_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2324_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
lean_ctor_set(v___x_2332_, 4, v___x_2330_);
lean_ctor_set(v___x_2332_, 5, v___x_2330_);
lean_ctor_set(v___x_2332_, 6, v___x_2330_);
lean_ctor_set(v___x_2332_, 7, v___x_2330_);
lean_ctor_set(v___x_2332_, 8, v___x_2330_);
lean_ctor_set(v___x_2332_, 9, v___x_2330_);
lean_ctor_set(v___x_2332_, 10, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2334_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_ctor_set(v___x_2334_, 2, v___x_2333_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
lean_ctor_set(v___x_2334_, 4, v___x_2333_);
lean_ctor_set(v___x_2334_, 5, v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
lean_ctor_set(v___x_2336_, 2, v___x_2335_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_ctor_set(v___x_2336_, 4, v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2346_, lean_object* v_ext_2347_, uint8_t v_showInfo_2348_, lean_object* v_attrName_2349_, lean_object* v_declName_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___y_2369_; 
v___x_2354_ = 1;
v___x_2355_ = 0;
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2361_ = lean_box(0);
lean_inc(v___x_2346_);
v___x_2362_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2362_, 0, v___x_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2346_);
lean_ctor_set(v___x_2362_, 2, v___x_2359_);
lean_ctor_set(v___x_2362_, 3, v___x_2360_);
lean_ctor_set(v___x_2362_, 4, v___x_2361_);
lean_ctor_set(v___x_2362_, 5, v___x_2357_);
lean_ctor_set(v___x_2362_, 6, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*7, v___x_2355_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*7 + 1, v___x_2355_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*7 + 2, v___x_2355_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*7 + 3, v___x_2354_);
v___x_2363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2364_);
lean_ctor_set(v___x_2366_, 2, v___x_2346_);
lean_ctor_set(v___x_2366_, 3, v___x_2358_);
lean_ctor_set(v___x_2366_, 4, v___x_2365_);
v___x_2367_ = lean_st_mk_ref(v___x_2366_);
if (v_showInfo_2348_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v_attrName_2349_);
v___x_2379_ = lean_box(0);
v___x_2380_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2350_, v_ext_2347_, v___x_2379_, v___x_2362_, v___x_2367_, v___y_2351_, v___y_2352_);
lean_dec_ref_known(v___x_2362_, 7);
v___y_2369_ = v___x_2380_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_declName_2350_);
lean_dec_ref(v_ext_2347_);
v___x_2381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2382_ = l_Lean_MessageData_ofName(v_attrName_2349_);
lean_inc_ref(v___x_2382_);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2382_);
v___x_2387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2388_, v___x_2362_, v___x_2367_, v___y_2351_, v___y_2352_);
lean_dec_ref_known(v___x_2362_, 7);
v___y_2369_ = v___x_2389_;
goto v___jp_2368_;
}
v___jp_2368_:
{
if (lean_obj_tag(v___y_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_a_2370_ = lean_ctor_get(v___y_2369_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___y_2369_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v___y_2369_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___y_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_st_ref_get(v___x_2367_);
lean_dec(v___x_2367_);
lean_dec(v___x_2374_);
if (v_isShared_2373_ == 0)
{
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2370_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_dec(v___x_2367_);
return v___y_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2390_, lean_object* v_ext_2391_, lean_object* v_showInfo_2392_, lean_object* v_attrName_2393_, lean_object* v_declName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v_showInfo_boxed_2398_; lean_object* v_res_2399_; 
v_showInfo_boxed_2398_ = lean_unbox(v_showInfo_2392_);
v_res_2399_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2390_, v_ext_2391_, v_showInfo_boxed_2398_, v_attrName_2393_, v_declName_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2402_, uint8_t v_attrKind_2403_, uint8_t v_showInfo_2404_, uint8_t v_minIndexable_2405_, lean_object* v_as_x27_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
if (lean_obj_tag(v_as_x27_2406_) == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref(v_ext_2402_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2407_);
return v___x_2413_;
}
else
{
lean_object* v_head_2414_; lean_object* v_tail_2415_; lean_object* v___x_2416_; 
v_head_2414_ = lean_ctor_get(v_as_x27_2406_, 0);
v_tail_2415_ = lean_ctor_get(v_as_x27_2406_, 1);
v___x_2416_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2411_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2414_);
lean_inc_ref(v_ext_2402_);
v___x_2419_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2402_, v_head_2414_, v_attrKind_2403_, v___x_2418_, v_a_2417_, v_showInfo_2404_, v_minIndexable_2405_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref_known(v___x_2419_, 1);
v___x_2420_ = lean_box(0);
v_as_x27_2406_ = v_tail_2415_;
v_b_2407_ = v___x_2420_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2402_);
return v___x_2419_;
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v_ext_2402_);
v_a_2422_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2416_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2416_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2430_, lean_object* v_attrKind_2431_, lean_object* v_showInfo_2432_, lean_object* v_minIndexable_2433_, lean_object* v_as_x27_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v_attrKind_boxed_2441_; uint8_t v_showInfo_boxed_2442_; uint8_t v_minIndexable_boxed_2443_; lean_object* v_res_2444_; 
v_attrKind_boxed_2441_ = lean_unbox(v_attrKind_2431_);
v_showInfo_boxed_2442_ = lean_unbox(v_showInfo_2432_);
v_minIndexable_boxed_2443_ = lean_unbox(v_minIndexable_2433_);
v_res_2444_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2430_, v_attrKind_boxed_2441_, v_showInfo_boxed_2442_, v_minIndexable_boxed_2443_, v_as_x27_2434_, v_b_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v_as_x27_2434_);
return v_res_2444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2447_ = l_Lean_stringToMessageData(v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2450_ = l_Lean_stringToMessageData(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2453_ = l_Lean_stringToMessageData(v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2456_ = l_Lean_stringToMessageData(v___x_2455_);
return v___x_2456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2462_ = l_Lean_stringToMessageData(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2475_, lean_object* v_ext_2476_, lean_object* v_declName_2477_, uint8_t v_attrKind_2478_, uint8_t v_showInfo_2479_, uint8_t v_minIndexable_2480_, uint8_t v___x_2481_, lean_object* v_attrName_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2475_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
switch(lean_obj_tag(v_a_2517_))
{
case 0:
{
lean_object* v_k_2518_; 
lean_dec(v_attrName_2482_);
lean_dec(v_stx_2475_);
v_k_2518_ = lean_ctor_get(v_a_2517_, 0);
lean_inc(v_k_2518_);
lean_dec_ref_known(v_a_2517_, 1);
if (lean_obj_tag(v_k_2518_) == 9)
{
lean_object* v___x_2519_; 
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
v___x_2519_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2485_, v___y_2486_);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2486_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2476_, v_declName_2477_, v_attrKind_2478_, v_k_2518_, v_a_2521_, v_showInfo_2479_, v_minIndexable_2480_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2522_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_k_2518_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
v_a_2523_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2520_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2520_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2531_; lean_object* v___x_2532_; 
lean_dec(v_attrName_2482_);
lean_dec(v_stx_2475_);
v_eager_2531_ = lean_ctor_get_uint8(v_a_2517_, 0);
lean_dec_ref_known(v_a_2517_, 0);
v___x_2532_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2476_, v_declName_2477_, v_eager_2531_, v_attrKind_2478_, v___y_2485_, v___y_2486_);
return v___x_2532_;
}
case 2:
{
lean_object* v___x_2533_; 
lean_dec(v_stx_2475_);
lean_inc(v_declName_2477_);
v___x_2533_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2477_, v___x_2481_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
if (lean_obj_tag(v_a_2534_) == 1)
{
lean_object* v_val_2535_; lean_object* v_ctors_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_attrName_2482_);
lean_dec(v_declName_2477_);
v_val_2535_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v_a_2534_, 1);
v_ctors_2536_ = lean_ctor_get(v_val_2535_, 4);
lean_inc(v_ctors_2536_);
lean_dec(v_val_2535_);
v___x_2537_ = lean_box(0);
v___x_2538_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2476_, v_attrKind_2478_, v_showInfo_2479_, v_minIndexable_2480_, v_ctors_2536_, v___x_2537_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v_ctors_2536_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; 
v_unused_2546_ = lean_ctor_get(v___x_2538_, 0);
lean_dec(v_unused_2546_);
v___x_2540_ = v___x_2538_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v___x_2538_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2537_);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2537_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v_a_2534_);
lean_dec_ref(v_ext_2476_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2548_ = l_Lean_MessageData_ofName(v_attrName_2482_);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_MessageData_ofConstName(v_declName_2477_, v___x_2481_);
v___x_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2555_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2556_;
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_attrName_2482_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
v_a_2557_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2533_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2533_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
case 3:
{
lean_object* v___x_2565_; 
lean_dec(v_attrName_2482_);
lean_inc(v_declName_2477_);
v___x_2565_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2477_, v___x_2481_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
if (lean_obj_tag(v_a_2566_) == 1)
{
lean_object* v_val_2567_; lean_object* v___x_2568_; 
lean_dec(v_declName_2477_);
lean_dec(v_stx_2475_);
v_val_2567_ = lean_ctor_get(v_a_2566_, 0);
lean_inc_n(v_val_2567_, 2);
lean_dec_ref_known(v_a_2566_, 1);
lean_inc_ref(v_ext_2476_);
v___x_2568_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2476_, v_val_2567_, v___x_2481_, v_attrKind_2478_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2569_; 
lean_dec_ref_known(v___x_2568_, 1);
v___x_2569_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2567_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2590_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2590_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2590_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
if (lean_obj_tag(v_a_2570_) == 1)
{
lean_object* v_val_2574_; lean_object* v_ctors_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_del_object(v___x_2572_);
v_val_2574_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v_a_2570_, 1);
v_ctors_2575_ = lean_ctor_get(v_val_2574_, 4);
lean_inc(v_ctors_2575_);
lean_dec(v_val_2574_);
v___x_2576_ = lean_box(0);
v___x_2577_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2476_, v_attrKind_2478_, v_showInfo_2479_, v_minIndexable_2480_, v_ctors_2575_, v___x_2576_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v_ctors_2575_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2585_);
v___x_2579_ = v___x_2577_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_dec(v___x_2577_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2576_);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2576_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
else
{
return v___x_2577_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_ext_2476_);
v___x_2586_ = lean_box(0);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2586_);
v___x_2588_ = v___x_2572_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_ext_2476_);
v_a_2591_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2569_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2569_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_dec(v_val_2567_);
lean_dec_ref(v_ext_2476_);
return v___x_2568_;
}
}
else
{
lean_object* v___x_2599_; 
lean_dec(v_a_2566_);
v___x_2599_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2486_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2476_, v_stx_2475_, v_declName_2477_, v_attrKind_2478_, v_a_2600_, v_minIndexable_2480_, v_showInfo_2479_, v___x_2481_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2601_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v_a_2602_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2599_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2599_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v_a_2610_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2565_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2565_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
case 4:
{
lean_object* v___x_2618_; 
lean_dec(v_attrName_2482_);
lean_dec(v_stx_2475_);
v___x_2618_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2476_, v_declName_2477_, v_attrKind_2478_, v___y_2485_, v___y_2486_);
return v___x_2618_;
}
case 5:
{
lean_object* v_prio_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v_prio_2619_ = lean_ctor_get(v_a_2517_, 0);
lean_inc(v_prio_2619_);
lean_dec_ref_known(v_a_2517_, 1);
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2621_ = lean_name_eq(v_attrName_2482_, v___x_2620_);
lean_dec(v_attrName_2482_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec(v_prio_2619_);
lean_dec(v_declName_2477_);
v___x_2622_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2623_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2622_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2623_;
}
else
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2477_, v_attrKind_2478_, v_prio_2619_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2624_;
}
}
case 6:
{
lean_object* v___x_2625_; 
lean_dec(v_attrName_2482_);
lean_dec(v_stx_2475_);
v___x_2625_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2476_, v_declName_2477_, v_attrKind_2478_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2625_;
}
case 7:
{
lean_object* v___x_2626_; 
lean_dec(v_attrName_2482_);
lean_dec(v_stx_2475_);
v___x_2626_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2476_, v_declName_2477_, v_attrKind_2478_, v___y_2485_, v___y_2486_);
return v___x_2626_;
}
case 8:
{
uint8_t v_post_2627_; uint8_t v_inv_2628_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v_post_2627_ = lean_ctor_get_uint8(v_a_2517_, 0);
v_inv_2628_ = lean_ctor_get_uint8(v_a_2517_, 1);
lean_dec_ref_known(v_a_2517_, 0);
v___x_2637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2638_ = lean_name_eq(v_attrName_2482_, v___x_2637_);
lean_dec(v_attrName_2482_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec(v_declName_2477_);
v___x_2639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2640_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2639_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2640_;
}
else
{
v___y_2630_ = v___y_2483_;
v___y_2631_ = v___y_2484_;
v___y_2632_ = v___y_2485_;
v___y_2633_ = v___y_2486_;
goto v___jp_2629_;
}
v___jp_2629_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = l_Lean_Meta_Grind_normExt;
v___x_2635_ = lean_unsigned_to_nat(1000u);
v___x_2636_ = l_Lean_Meta_addSimpTheorem(v___x_2634_, v_declName_2477_, v_post_2627_, v_inv_2628_, v_attrKind_2478_, v___x_2635_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2636_;
}
}
case 9:
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2642_ = lean_name_eq(v_attrName_2482_, v___x_2641_);
lean_dec(v_attrName_2482_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v_declName_2477_);
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2644_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2643_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2644_;
}
else
{
v___y_2489_ = v___y_2483_;
v___y_2490_ = v___y_2484_;
v___y_2491_ = v___y_2485_;
v___y_2492_ = v___y_2486_;
goto v___jp_2488_;
}
}
case 10:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2646_ = lean_name_eq(v_attrName_2482_, v___x_2645_);
lean_dec(v_attrName_2482_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec(v_declName_2477_);
v___x_2647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2648_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2647_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2477_, v_attrKind_2478_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2649_;
}
}
default: 
{
lean_object* v___x_2650_; uint8_t v___x_2651_; 
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2651_ = lean_name_eq(v_attrName_2482_, v___x_2650_);
lean_dec(v_attrName_2482_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec(v_declName_2477_);
v___x_2652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2653_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2652_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2477_, v_attrKind_2478_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_attrName_2482_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_ext_2476_);
lean_dec(v_stx_2475_);
v_a_2655_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2516_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2516_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
v___jp_2488_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = l_Lean_Meta_Grind_normExt;
v___x_2494_ = lean_unsigned_to_nat(1000u);
v___x_2495_ = l_Lean_Meta_addDeclToUnfold(v___x_2493_, v_declName_2477_, v___x_2481_, v___x_2481_, v___x_2494_, v_attrKind_2478_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2507_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_del_object(v___x_2498_);
v___x_2501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2502_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2501_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(0);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2503_);
v___x_2505_ = v___x_2498_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2495_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2495_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2663_, lean_object* v_ext_2664_, lean_object* v_declName_2665_, lean_object* v_attrKind_2666_, lean_object* v_showInfo_2667_, lean_object* v_minIndexable_2668_, lean_object* v___x_2669_, lean_object* v_attrName_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
uint8_t v_attrKind_boxed_2676_; uint8_t v_showInfo_boxed_2677_; uint8_t v_minIndexable_boxed_2678_; uint8_t v___x_15060__boxed_2679_; lean_object* v_res_2680_; 
v_attrKind_boxed_2676_ = lean_unbox(v_attrKind_2666_);
v_showInfo_boxed_2677_ = lean_unbox(v_showInfo_2667_);
v_minIndexable_boxed_2678_ = lean_unbox(v_minIndexable_2668_);
v___x_15060__boxed_2679_ = lean_unbox(v___x_2669_);
v_res_2680_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2663_, v_ext_2664_, v_declName_2665_, v_attrKind_boxed_2676_, v_showInfo_boxed_2677_, v_minIndexable_boxed_2678_, v___x_15060__boxed_2679_, v_attrName_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2680_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2681_; double v___x_2682_; 
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = lean_float_of_nat(v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2686_, lean_object* v_msg_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_ref_2693_; lean_object* v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2739_; 
v_ref_2693_ = lean_ctor_get(v___y_2690_, 2);
v___x_2694_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2739_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2739_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v_traceState_2700_; lean_object* v_env_2701_; lean_object* v_nextMacroScope_2702_; lean_object* v_ngen_2703_; lean_object* v_auxDeclNGen_2704_; lean_object* v_cache_2705_; lean_object* v_messages_2706_; lean_object* v_infoState_2707_; lean_object* v_snapshotTasks_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2738_; 
v___x_2699_ = lean_st_ref_take(v___y_2691_);
v_traceState_2700_ = lean_ctor_get(v___x_2699_, 4);
v_env_2701_ = lean_ctor_get(v___x_2699_, 0);
v_nextMacroScope_2702_ = lean_ctor_get(v___x_2699_, 1);
v_ngen_2703_ = lean_ctor_get(v___x_2699_, 2);
v_auxDeclNGen_2704_ = lean_ctor_get(v___x_2699_, 3);
v_cache_2705_ = lean_ctor_get(v___x_2699_, 5);
v_messages_2706_ = lean_ctor_get(v___x_2699_, 6);
v_infoState_2707_ = lean_ctor_get(v___x_2699_, 7);
v_snapshotTasks_2708_ = lean_ctor_get(v___x_2699_, 8);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2710_ = v___x_2699_;
v_isShared_2711_ = v_isSharedCheck_2738_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_snapshotTasks_2708_);
lean_inc(v_infoState_2707_);
lean_inc(v_messages_2706_);
lean_inc(v_cache_2705_);
lean_inc(v_traceState_2700_);
lean_inc(v_auxDeclNGen_2704_);
lean_inc(v_ngen_2703_);
lean_inc(v_nextMacroScope_2702_);
lean_inc(v_env_2701_);
lean_dec(v___x_2699_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2738_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
uint64_t v_tid_2712_; lean_object* v_traces_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2737_; 
v_tid_2712_ = lean_ctor_get_uint64(v_traceState_2700_, sizeof(void*)*1);
v_traces_2713_ = lean_ctor_get(v_traceState_2700_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_traceState_2700_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2715_ = v_traceState_2700_;
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_traces_2713_);
lean_dec(v_traceState_2700_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2737_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; double v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2719_ = 0;
v___x_2720_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2721_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2721_, 0, v_cls_2686_);
lean_ctor_set(v___x_2721_, 1, v___x_2717_);
lean_ctor_set(v___x_2721_, 2, v___x_2720_);
lean_ctor_set_float(v___x_2721_, sizeof(void*)*3, v___x_2718_);
lean_ctor_set_float(v___x_2721_, sizeof(void*)*3 + 8, v___x_2718_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*3 + 16, v___x_2719_);
v___x_2722_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2723_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v_a_2695_);
lean_ctor_set(v___x_2723_, 2, v___x_2722_);
lean_inc(v_ref_2693_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_ref_2693_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = l_Lean_PersistentArray_push___redArg(v_traces_2713_, v___x_2724_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2725_);
v___x_2727_ = v___x_2715_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2725_);
lean_ctor_set_uint64(v_reuseFailAlloc_2736_, sizeof(void*)*1, v_tid_2712_);
v___x_2727_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 4, v___x_2727_);
v___x_2729_ = v___x_2710_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_env_2701_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_nextMacroScope_2702_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_ngen_2703_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_auxDeclNGen_2704_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2735_, 5, v_cache_2705_);
lean_ctor_set(v_reuseFailAlloc_2735_, 6, v_messages_2706_);
lean_ctor_set(v_reuseFailAlloc_2735_, 7, v_infoState_2707_);
lean_ctor_set(v_reuseFailAlloc_2735_, 8, v_snapshotTasks_2708_);
v___x_2729_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = lean_st_ref_put(v___y_2691_, v___x_2729_);
v___x_2731_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2731_);
v___x_2733_ = v___x_2697_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2740_, lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2740_, v_msg_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2748_, lean_object* v_i_2749_, lean_object* v_k_2750_){
_start:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = lean_array_get_size(v_keys_2748_);
v___x_2752_ = lean_nat_dec_lt(v_i_2749_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_dec(v_i_2749_);
return v___x_2752_;
}
else
{
lean_object* v_k_x27_2753_; uint8_t v___x_2754_; 
v_k_x27_2753_ = lean_array_fget_borrowed(v_keys_2748_, v_i_2749_);
v___x_2754_ = l_Lean_instBEqExtraModUse_beq(v_k_2750_, v_k_x27_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_nat_add(v_i_2749_, v___x_2755_);
lean_dec(v_i_2749_);
v_i_2749_ = v___x_2756_;
goto _start;
}
else
{
lean_dec(v_i_2749_);
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2758_, lean_object* v_i_2759_, lean_object* v_k_2760_){
_start:
{
uint8_t v_res_2761_; lean_object* v_r_2762_; 
v_res_2761_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2758_, v_i_2759_, v_k_2760_);
lean_dec_ref(v_k_2760_);
lean_dec_ref(v_keys_2758_);
v_r_2762_ = lean_box(v_res_2761_);
return v_r_2762_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2763_, size_t v_x_2764_, lean_object* v_x_2765_){
_start:
{
if (lean_obj_tag(v_x_2763_) == 0)
{
lean_object* v_es_2766_; lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; lean_object* v_j_2770_; lean_object* v___x_2771_; 
v_es_2766_ = lean_ctor_get(v_x_2763_, 0);
v___x_2767_ = lean_box(2);
v___x_2768_ = ((size_t)31ULL);
v___x_2769_ = lean_usize_land(v_x_2764_, v___x_2768_);
v_j_2770_ = lean_usize_to_nat(v___x_2769_);
v___x_2771_ = lean_array_get_borrowed(v___x_2767_, v_es_2766_, v_j_2770_);
lean_dec(v_j_2770_);
switch(lean_obj_tag(v___x_2771_))
{
case 0:
{
lean_object* v_key_2772_; uint8_t v___x_2773_; 
v_key_2772_ = lean_ctor_get(v___x_2771_, 0);
v___x_2773_ = l_Lean_instBEqExtraModUse_beq(v_x_2765_, v_key_2772_);
return v___x_2773_;
}
case 1:
{
lean_object* v_node_2774_; size_t v___x_2775_; size_t v___x_2776_; 
v_node_2774_ = lean_ctor_get(v___x_2771_, 0);
v___x_2775_ = ((size_t)5ULL);
v___x_2776_ = lean_usize_shift_right(v_x_2764_, v___x_2775_);
v_x_2763_ = v_node_2774_;
v_x_2764_ = v___x_2776_;
goto _start;
}
default: 
{
uint8_t v___x_2778_; 
v___x_2778_ = 0;
return v___x_2778_;
}
}
}
else
{
lean_object* v_ks_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_ks_2779_ = lean_ctor_get(v_x_2763_, 0);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2779_, v___x_2780_, v_x_2765_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
size_t v_x_15584__boxed_2785_; uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_x_15584__boxed_2785_ = lean_unbox_usize(v_x_2783_);
lean_dec(v_x_2783_);
v_res_2786_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2782_, v_x_15584__boxed_2785_, v_x_2784_);
lean_dec_ref(v_x_2784_);
lean_dec_ref(v_x_2782_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2788_, lean_object* v_x_2789_){
_start:
{
uint64_t v___x_2790_; size_t v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = l_Lean_instHashableExtraModUse_hash(v_x_2789_);
v___x_2791_ = lean_uint64_to_usize(v___x_2790_);
v___x_2792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2788_, v___x_2791_, v_x_2789_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
uint8_t v_res_2795_; lean_object* v_r_2796_; 
v_res_2795_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2793_, v_x_2794_);
lean_dec_ref(v_x_2794_);
lean_dec_ref(v_x_2793_);
v_r_2796_ = lean_box(v_res_2795_);
return v_r_2796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2800_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2801_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2800_, v___x_2799_);
return v___x_2801_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2810_ = l_Lean_stringToMessageData(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_cls_2816_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2817_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2818_ = l_Lean_Name_append(v___x_2817_, v_cls_2816_);
return v___x_2818_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2821_ = l_Lean_stringToMessageData(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2829_, uint8_t v_isMeta_2830_, lean_object* v_hint_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v_env_2838_; uint8_t v_isExporting_2839_; lean_object* v___x_2840_; lean_object* v_env_2841_; lean_object* v___x_2842_; lean_object* v_entry_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2837_ = lean_st_ref_get(v___y_2835_);
v_env_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc_ref(v_env_2838_);
lean_dec(v___x_2837_);
v_isExporting_2839_ = lean_ctor_get_uint8(v_env_2838_, sizeof(void*)*8);
lean_dec_ref(v_env_2838_);
v___x_2840_ = lean_st_ref_get(v___y_2835_);
v_env_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_ref(v_env_2841_);
lean_dec(v___x_2840_);
v___x_2842_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2829_);
v_entry_2843_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2843_, 0, v_mod_2829_);
lean_ctor_set_uint8(v_entry_2843_, sizeof(void*)*1, v_isExporting_2839_);
lean_ctor_set_uint8(v_entry_2843_, sizeof(void*)*1 + 1, v_isMeta_2830_);
v___x_2844_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2845_ = lean_box(1);
v___x_2846_ = lean_box(0);
v___x_2889_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2842_, v___x_2844_, v_env_2841_, v___x_2845_, v___x_2846_);
v___x_2890_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2889_, v_entry_2843_);
lean_dec(v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v_toCold_2891_; lean_object* v_options_2892_; uint8_t v_hasTrace_2893_; 
v_toCold_2891_ = lean_ctor_get(v___y_2834_, 0);
v_options_2892_ = lean_ctor_get(v_toCold_2891_, 2);
v_hasTrace_2893_ = lean_ctor_get_uint8(v_options_2892_, sizeof(void*)*1);
if (v_hasTrace_2893_ == 0)
{
lean_dec(v_hint_2831_);
lean_dec(v_mod_2829_);
v___y_2848_ = v___y_2833_;
v___y_2849_ = v___y_2835_;
goto v___jp_2847_;
}
else
{
lean_object* v_inheritedTraceOptions_2894_; lean_object* v_cls_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_inheritedTraceOptions_2894_ = lean_ctor_get(v_toCold_2891_, 11);
v_cls_2895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2915_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2894_, v_options_2892_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_dec(v_hint_2831_);
lean_dec(v_mod_2829_);
v___y_2848_ = v___y_2833_;
v___y_2849_ = v___y_2835_;
goto v___jp_2847_;
}
else
{
lean_object* v___x_2917_; lean_object* v___y_2919_; 
v___x_2917_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2839_ == 0)
{
lean_object* v___x_2926_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2919_ = v___x_2926_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2927_; 
v___x_2927_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2919_ = v___x_2927_;
goto v___jp_2918_;
}
v___jp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_inc_ref(v___y_2919_);
v___x_2920_ = l_Lean_stringToMessageData(v___y_2919_);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2917_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
if (v_isMeta_2830_ == 0)
{
lean_object* v___x_2924_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2902_ = v___x_2923_;
v___y_2903_ = v___x_2924_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2925_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2902_ = v___x_2923_;
v___y_2903_ = v___x_2925_;
goto v___jp_2901_;
}
}
}
v___jp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___y_2897_);
lean_ctor_set(v___x_2899_, 1, v___y_2898_);
v___x_2900_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2895_, v___x_2899_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_dec_ref_known(v___x_2900_, 1);
v___y_2848_ = v___y_2833_;
v___y_2849_ = v___y_2835_;
goto v___jp_2847_;
}
else
{
lean_dec_ref_known(v_entry_2843_, 1);
return v___x_2900_;
}
}
v___jp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
lean_inc_ref(v___y_2903_);
v___x_2904_ = l_Lean_stringToMessageData(v___y_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2902_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_MessageData_ofName(v_mod_2829_);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Lean_Name_isAnonymous(v_hint_2831_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2912_ = l_Lean_MessageData_ofName(v_hint_2831_);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___y_2897_ = v___x_2909_;
v___y_2898_ = v___x_2913_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_hint_2831_);
v___x_2914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2897_ = v___x_2909_;
v___y_2898_ = v___x_2914_;
goto v___jp_2896_;
}
}
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec_ref_known(v_entry_2843_, 1);
lean_dec(v_hint_2831_);
lean_dec(v_mod_2829_);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
v___jp_2847_:
{
lean_object* v___x_2850_; lean_object* v_toEnvExtension_2851_; lean_object* v_env_2852_; lean_object* v_nextMacroScope_2853_; lean_object* v_ngen_2854_; lean_object* v_auxDeclNGen_2855_; lean_object* v_traceState_2856_; lean_object* v_messages_2857_; lean_object* v_infoState_2858_; lean_object* v_snapshotTasks_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2887_; 
v___x_2850_ = lean_st_ref_take(v___y_2849_);
v_toEnvExtension_2851_ = lean_ctor_get(v___x_2844_, 0);
v_env_2852_ = lean_ctor_get(v___x_2850_, 0);
v_nextMacroScope_2853_ = lean_ctor_get(v___x_2850_, 1);
v_ngen_2854_ = lean_ctor_get(v___x_2850_, 2);
v_auxDeclNGen_2855_ = lean_ctor_get(v___x_2850_, 3);
v_traceState_2856_ = lean_ctor_get(v___x_2850_, 4);
v_messages_2857_ = lean_ctor_get(v___x_2850_, 6);
v_infoState_2858_ = lean_ctor_get(v___x_2850_, 7);
v_snapshotTasks_2859_ = lean_ctor_get(v___x_2850_, 8);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2850_, 5);
lean_dec(v_unused_2888_);
v___x_2861_ = v___x_2850_;
v_isShared_2862_ = v_isSharedCheck_2887_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_snapshotTasks_2859_);
lean_inc(v_infoState_2858_);
lean_inc(v_messages_2857_);
lean_inc(v_traceState_2856_);
lean_inc(v_auxDeclNGen_2855_);
lean_inc(v_ngen_2854_);
lean_inc(v_nextMacroScope_2853_);
lean_inc(v_env_2852_);
lean_dec(v___x_2850_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2887_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_asyncMode_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v_asyncMode_2863_ = lean_ctor_get(v_toEnvExtension_2851_, 2);
v___x_2864_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2844_, v_env_2852_, v_entry_2843_, v_asyncMode_2863_, v___x_2846_);
v___x_2865_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 5, v___x_2865_);
lean_ctor_set(v___x_2861_, 0, v___x_2864_);
v___x_2867_ = v___x_2861_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_nextMacroScope_2853_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_ngen_2854_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_auxDeclNGen_2855_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_traceState_2856_);
lean_ctor_set(v_reuseFailAlloc_2886_, 5, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2886_, 6, v_messages_2857_);
lean_ctor_set(v_reuseFailAlloc_2886_, 7, v_infoState_2858_);
lean_ctor_set(v_reuseFailAlloc_2886_, 8, v_snapshotTasks_2859_);
v___x_2867_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_mctx_2870_; lean_object* v_zetaDeltaFVarIds_2871_; lean_object* v_postponed_2872_; lean_object* v_diag_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2884_; 
v___x_2868_ = lean_st_ref_put(v___y_2849_, v___x_2867_);
v___x_2869_ = lean_st_ref_take(v___y_2848_);
v_mctx_2870_ = lean_ctor_get(v___x_2869_, 0);
v_zetaDeltaFVarIds_2871_ = lean_ctor_get(v___x_2869_, 2);
v_postponed_2872_ = lean_ctor_get(v___x_2869_, 3);
v_diag_2873_ = lean_ctor_get(v___x_2869_, 4);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2869_, 1);
lean_dec(v_unused_2885_);
v___x_2875_ = v___x_2869_;
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_diag_2873_);
lean_inc(v_postponed_2872_);
lean_inc(v_zetaDeltaFVarIds_2871_);
lean_inc(v_mctx_2870_);
lean_dec(v___x_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2884_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_mctx_2870_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_zetaDeltaFVarIds_2871_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_postponed_2872_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_diag_2873_);
v___x_2879_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_st_ref_put(v___y_2848_, v___x_2879_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2930_, lean_object* v_isMeta_2931_, lean_object* v_hint_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_isMeta_boxed_2938_; lean_object* v_res_2939_; 
v_isMeta_boxed_2938_ = lean_unbox(v_isMeta_2931_);
v_res_2939_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2930_, v_isMeta_boxed_2938_, v_hint_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
else
{
lean_object* v_key_2943_; lean_object* v_value_2944_; lean_object* v_tail_2945_; uint8_t v___x_2946_; 
v_key_2943_ = lean_ctor_get(v_x_2941_, 0);
v_value_2944_ = lean_ctor_get(v_x_2941_, 1);
v_tail_2945_ = lean_ctor_get(v_x_2941_, 2);
v___x_2946_ = lean_name_eq(v_key_2943_, v_a_2940_);
if (v___x_2946_ == 0)
{
v_x_2941_ = v_tail_2945_;
goto _start;
}
else
{
lean_object* v___x_2948_; 
lean_inc(v_value_2944_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_value_2944_);
return v___x_2948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2949_, v_x_2950_);
lean_dec(v_x_2950_);
lean_dec(v_a_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_buckets_2954_; lean_object* v___x_2955_; uint64_t v___y_2957_; 
v_buckets_2954_ = lean_ctor_get(v_m_2952_, 1);
v___x_2955_ = lean_array_get_size(v_buckets_2954_);
if (lean_obj_tag(v_a_2953_) == 0)
{
uint64_t v___x_2971_; 
v___x_2971_ = 1723ULL;
v___y_2957_ = v___x_2971_;
goto v___jp_2956_;
}
else
{
uint64_t v_hash_2972_; 
v_hash_2972_ = lean_ctor_get_uint64(v_a_2953_, sizeof(void*)*2);
v___y_2957_ = v_hash_2972_;
goto v___jp_2956_;
}
v___jp_2956_:
{
uint64_t v___x_2958_; uint64_t v___x_2959_; uint64_t v_fold_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint64_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2958_ = 32ULL;
v___x_2959_ = lean_uint64_shift_right(v___y_2957_, v___x_2958_);
v_fold_2960_ = lean_uint64_xor(v___y_2957_, v___x_2959_);
v___x_2961_ = 16ULL;
v___x_2962_ = lean_uint64_shift_right(v_fold_2960_, v___x_2961_);
v___x_2963_ = lean_uint64_xor(v_fold_2960_, v___x_2962_);
v___x_2964_ = lean_uint64_to_usize(v___x_2963_);
v___x_2965_ = lean_usize_of_nat(v___x_2955_);
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_sub(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_usize_land(v___x_2964_, v___x_2967_);
v___x_2969_ = lean_array_uget_borrowed(v_buckets_2954_, v___x_2968_);
v___x_2970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2953_, v___x_2969_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2973_, v_a_2974_);
lean_dec(v_a_2974_);
lean_dec_ref(v_m_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2976_, lean_object* v_declName_2977_, lean_object* v_as_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
lean_dec(v_declName_2977_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_b_2981_);
return v___x_2988_;
}
else
{
lean_object* v___x_2989_; lean_object* v_modules_2990_; lean_object* v___x_2991_; lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v_toImport_2994_; lean_object* v_module_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2989_ = l_Lean_Environment_header(v___x_2976_);
v_modules_2990_ = lean_ctor_get(v___x_2989_, 3);
lean_inc_ref(v_modules_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2992_ = lean_array_uget_borrowed(v_as_2978_, v_i_2980_);
v___x_2993_ = lean_array_get(v___x_2991_, v_modules_2990_, v_a_2992_);
lean_dec_ref(v_modules_2990_);
v_toImport_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc_ref(v_toImport_2994_);
lean_dec(v___x_2993_);
v_module_2995_ = lean_ctor_get(v_toImport_2994_, 0);
lean_inc(v_module_2995_);
lean_dec_ref(v_toImport_2994_);
v___x_2996_ = 0;
lean_inc(v_declName_2977_);
v___x_2997_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2995_, v___x_2996_, v_declName_2977_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; 
lean_dec_ref_known(v___x_2997_, 1);
v___x_2998_ = lean_box(0);
v___x_2999_ = ((size_t)1ULL);
v___x_3000_ = lean_usize_add(v_i_2980_, v___x_2999_);
v_i_2980_ = v___x_3000_;
v_b_2981_ = v___x_2998_;
goto _start;
}
else
{
lean_dec(v_declName_2977_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3002_, lean_object* v_declName_3003_, lean_object* v_as_3004_, lean_object* v_sz_3005_, lean_object* v_i_3006_, lean_object* v_b_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
size_t v_sz_boxed_3013_; size_t v_i_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3013_ = lean_unbox_usize(v_sz_3005_);
lean_dec(v_sz_3005_);
v_i_boxed_3014_ = lean_unbox_usize(v_i_3006_);
lean_dec(v_i_3006_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3002_, v_declName_3003_, v_as_3004_, v_sz_boxed_3013_, v_i_boxed_3014_, v_b_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec_ref(v_as_3004_);
lean_dec_ref(v___x_3002_);
return v_res_3015_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_3019_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_3020_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3023_, uint8_t v_isMeta_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; lean_object* v_env_3034_; lean_object* v___y_3036_; lean_object* v___x_3049_; 
v___x_3030_ = lean_st_ref_get(v___y_3028_);
v_env_3034_ = lean_ctor_get(v___x_3030_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3030_);
v___x_3049_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3034_, v_declName_3023_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref(v_env_3034_);
lean_dec(v_declName_3023_);
goto v___jp_3031_;
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3051_; lean_object* v_modules_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v_val_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3051_ = l_Lean_Environment_header(v_env_3034_);
v_modules_3052_ = lean_ctor_get(v___x_3051_, 3);
lean_inc_ref(v_modules_3052_);
lean_dec_ref(v___x_3051_);
v___x_3053_ = lean_array_get_size(v_modules_3052_);
v___x_3054_ = lean_nat_dec_lt(v_val_3050_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_dec_ref(v_modules_3052_);
lean_dec(v_val_3050_);
lean_dec_ref(v_env_3034_);
lean_dec(v_declName_3023_);
goto v___jp_3031_;
}
else
{
lean_object* v___x_3055_; lean_object* v_env_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___y_3060_; 
v___x_3055_ = lean_st_ref_get(v___y_3028_);
v_env_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_ref(v_env_3056_);
lean_dec(v___x_3055_);
v___x_3057_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3058_ = lean_array_fget(v_modules_3052_, v_val_3050_);
lean_dec(v_val_3050_);
lean_dec_ref(v_modules_3052_);
if (v_isMeta_3024_ == 0)
{
lean_dec_ref(v_env_3056_);
v___y_3060_ = v_isMeta_3024_;
goto v___jp_3059_;
}
else
{
uint8_t v___x_3071_; 
lean_inc(v_declName_3023_);
v___x_3071_ = l_Lean_isMarkedMeta(v_env_3056_, v_declName_3023_);
if (v___x_3071_ == 0)
{
v___y_3060_ = v_isMeta_3024_;
goto v___jp_3059_;
}
else
{
uint8_t v___x_3072_; 
v___x_3072_ = 0;
v___y_3060_ = v___x_3072_;
goto v___jp_3059_;
}
}
v___jp_3059_:
{
lean_object* v_toImport_3061_; lean_object* v_module_3062_; lean_object* v___x_3063_; 
v_toImport_3061_ = lean_ctor_get(v___x_3058_, 0);
lean_inc_ref(v_toImport_3061_);
lean_dec(v___x_3058_);
v_module_3062_ = lean_ctor_get(v_toImport_3061_, 0);
lean_inc(v_module_3062_);
lean_dec_ref(v_toImport_3061_);
lean_inc(v_declName_3023_);
v___x_3063_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3062_, v___y_3060_, v_declName_3023_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref_known(v___x_3063_, 1);
v___x_3064_ = l_Lean_indirectModUseExt;
v___x_3065_ = lean_box(1);
v___x_3066_ = lean_box(0);
lean_inc_ref(v_env_3034_);
v___x_3067_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3057_, v___x_3064_, v_env_3034_, v___x_3065_, v___x_3066_);
v___x_3068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3067_, v_declName_3023_);
lean_dec(v___x_3067_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3036_ = v___x_3069_;
goto v___jp_3035_;
}
else
{
lean_object* v_val_3070_; 
v_val_3070_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3070_);
lean_dec_ref_known(v___x_3068_, 1);
v___y_3036_ = v_val_3070_;
goto v___jp_3035_;
}
}
else
{
lean_dec_ref(v_env_3034_);
lean_dec(v_declName_3023_);
return v___x_3063_;
}
}
}
}
v___jp_3031_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
v___jp_3035_:
{
lean_object* v___x_3037_; size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3037_ = lean_box(0);
v_sz_3038_ = lean_array_size(v___y_3036_);
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3034_, v_declName_3023_, v___y_3036_, v_sz_3038_, v___x_3039_, v___x_3037_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec_ref(v___y_3036_);
lean_dec_ref(v_env_3034_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3048_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3037_);
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3037_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
return v___x_3040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3073_, lean_object* v_isMeta_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
uint8_t v_isMeta_boxed_3080_; lean_object* v_res_3081_; 
v_isMeta_boxed_3080_ = lean_unbox(v_isMeta_3074_);
v_res_3081_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3073_, v_isMeta_boxed_3080_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3082_, uint8_t v_isExporting_3083_, lean_object* v___x_3084_, lean_object* v___y_3085_, lean_object* v___x_3086_, lean_object* v_a_x3f_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v_nextMacroScope_3091_; lean_object* v_ngen_3092_; lean_object* v_auxDeclNGen_3093_; lean_object* v_traceState_3094_; lean_object* v_messages_3095_; lean_object* v_infoState_3096_; lean_object* v_snapshotTasks_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3122_; 
v___x_3089_ = lean_st_ref_take(v___y_3082_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
v_nextMacroScope_3091_ = lean_ctor_get(v___x_3089_, 1);
v_ngen_3092_ = lean_ctor_get(v___x_3089_, 2);
v_auxDeclNGen_3093_ = lean_ctor_get(v___x_3089_, 3);
v_traceState_3094_ = lean_ctor_get(v___x_3089_, 4);
v_messages_3095_ = lean_ctor_get(v___x_3089_, 6);
v_infoState_3096_ = lean_ctor_get(v___x_3089_, 7);
v_snapshotTasks_3097_ = lean_ctor_get(v___x_3089_, 8);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v___x_3089_, 5);
lean_dec(v_unused_3123_);
v___x_3099_ = v___x_3089_;
v_isShared_3100_ = v_isSharedCheck_3122_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_snapshotTasks_3097_);
lean_inc(v_infoState_3096_);
lean_inc(v_messages_3095_);
lean_inc(v_traceState_3094_);
lean_inc(v_auxDeclNGen_3093_);
lean_inc(v_ngen_3092_);
lean_inc(v_nextMacroScope_3091_);
lean_inc(v_env_3090_);
lean_dec(v___x_3089_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3122_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = l_Lean_Environment_setExporting(v_env_3090_, v_isExporting_3083_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 5, v___x_3084_);
lean_ctor_set(v___x_3099_, 0, v___x_3101_);
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_nextMacroScope_3091_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_ngen_3092_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_auxDeclNGen_3093_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_traceState_3094_);
lean_ctor_set(v_reuseFailAlloc_3121_, 5, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3121_, 6, v_messages_3095_);
lean_ctor_set(v_reuseFailAlloc_3121_, 7, v_infoState_3096_);
lean_ctor_set(v_reuseFailAlloc_3121_, 8, v_snapshotTasks_3097_);
v___x_3103_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_mctx_3106_; lean_object* v_zetaDeltaFVarIds_3107_; lean_object* v_postponed_3108_; lean_object* v_diag_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3119_; 
v___x_3104_ = lean_st_ref_put(v___y_3082_, v___x_3103_);
v___x_3105_ = lean_st_ref_take(v___y_3085_);
v_mctx_3106_ = lean_ctor_get(v___x_3105_, 0);
v_zetaDeltaFVarIds_3107_ = lean_ctor_get(v___x_3105_, 2);
v_postponed_3108_ = lean_ctor_get(v___x_3105_, 3);
v_diag_3109_ = lean_ctor_get(v___x_3105_, 4);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3105_, 1);
lean_dec(v_unused_3120_);
v___x_3111_ = v___x_3105_;
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_diag_3109_);
lean_inc(v_postponed_3108_);
lean_inc(v_zetaDeltaFVarIds_3107_);
lean_inc(v_mctx_3106_);
lean_dec(v___x_3105_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3086_);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_mctx_3106_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v_zetaDeltaFVarIds_3107_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v_postponed_3108_);
lean_ctor_set(v_reuseFailAlloc_3118_, 4, v_diag_3109_);
v___x_3114_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_st_ref_put(v___y_3085_, v___x_3114_);
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
return v___x_3117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3124_, lean_object* v_isExporting_3125_, lean_object* v___x_3126_, lean_object* v___y_3127_, lean_object* v___x_3128_, lean_object* v_a_x3f_3129_, lean_object* v___y_3130_){
_start:
{
uint8_t v_isExporting_boxed_3131_; lean_object* v_res_3132_; 
v_isExporting_boxed_3131_ = lean_unbox(v_isExporting_3125_);
v_res_3132_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3124_, v_isExporting_boxed_3131_, v___x_3126_, v___y_3127_, v___x_3128_, v_a_x3f_3129_);
lean_dec(v_a_x3f_3129_);
lean_dec(v___y_3127_);
lean_dec(v___y_3124_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3133_, uint8_t v_isExporting_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v_env_3141_; lean_object* v___x_3142_; uint8_t v_isModule_3143_; 
v___x_3140_ = lean_st_ref_get(v___y_3138_);
v_env_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc_ref(v_env_3141_);
lean_dec(v___x_3140_);
v___x_3142_ = l_Lean_Environment_header(v_env_3141_);
v_isModule_3143_ = lean_ctor_get_uint8(v___x_3142_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3142_);
if (v_isModule_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec_ref(v_env_3141_);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
v___x_3144_ = lean_apply_5(v_x_3133_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
return v___x_3144_;
}
else
{
uint8_t v_isExporting_3145_; 
v_isExporting_3145_ = lean_ctor_get_uint8(v_env_3141_, sizeof(void*)*8);
lean_dec_ref(v_env_3141_);
if (v_isExporting_3134_ == 0)
{
if (v_isExporting_3145_ == 0)
{
lean_object* v___x_3211_; 
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
v___x_3211_ = lean_apply_5(v_x_3133_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
return v___x_3211_;
}
else
{
goto v___jp_3146_;
}
}
else
{
if (v_isExporting_3145_ == 0)
{
goto v___jp_3146_;
}
else
{
lean_object* v___x_3212_; 
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
v___x_3212_ = lean_apply_5(v_x_3133_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
return v___x_3212_;
}
}
v___jp_3146_:
{
lean_object* v___x_3147_; lean_object* v_env_3148_; lean_object* v_nextMacroScope_3149_; lean_object* v_ngen_3150_; lean_object* v_auxDeclNGen_3151_; lean_object* v_traceState_3152_; lean_object* v_messages_3153_; lean_object* v_infoState_3154_; lean_object* v_snapshotTasks_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3209_; 
v___x_3147_ = lean_st_ref_take(v___y_3138_);
v_env_3148_ = lean_ctor_get(v___x_3147_, 0);
v_nextMacroScope_3149_ = lean_ctor_get(v___x_3147_, 1);
v_ngen_3150_ = lean_ctor_get(v___x_3147_, 2);
v_auxDeclNGen_3151_ = lean_ctor_get(v___x_3147_, 3);
v_traceState_3152_ = lean_ctor_get(v___x_3147_, 4);
v_messages_3153_ = lean_ctor_get(v___x_3147_, 6);
v_infoState_3154_ = lean_ctor_get(v___x_3147_, 7);
v_snapshotTasks_3155_ = lean_ctor_get(v___x_3147_, 8);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3147_, 5);
lean_dec(v_unused_3210_);
v___x_3157_ = v___x_3147_;
v_isShared_3158_ = v_isSharedCheck_3209_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_snapshotTasks_3155_);
lean_inc(v_infoState_3154_);
lean_inc(v_messages_3153_);
lean_inc(v_traceState_3152_);
lean_inc(v_auxDeclNGen_3151_);
lean_inc(v_ngen_3150_);
lean_inc(v_nextMacroScope_3149_);
lean_inc(v_env_3148_);
lean_dec(v___x_3147_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3209_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3159_ = l_Lean_Environment_setExporting(v_env_3148_, v_isExporting_3134_);
v___x_3160_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 5, v___x_3160_);
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_nextMacroScope_3149_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_ngen_3150_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_auxDeclNGen_3151_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_traceState_3152_);
lean_ctor_set(v_reuseFailAlloc_3208_, 5, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3208_, 6, v_messages_3153_);
lean_ctor_set(v_reuseFailAlloc_3208_, 7, v_infoState_3154_);
lean_ctor_set(v_reuseFailAlloc_3208_, 8, v_snapshotTasks_3155_);
v___x_3162_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_mctx_3165_; lean_object* v_zetaDeltaFVarIds_3166_; lean_object* v_postponed_3167_; lean_object* v_diag_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3206_; 
v___x_3163_ = lean_st_ref_put(v___y_3138_, v___x_3162_);
v___x_3164_ = lean_st_ref_take(v___y_3136_);
v_mctx_3165_ = lean_ctor_get(v___x_3164_, 0);
v_zetaDeltaFVarIds_3166_ = lean_ctor_get(v___x_3164_, 2);
v_postponed_3167_ = lean_ctor_get(v___x_3164_, 3);
v_diag_3168_ = lean_ctor_get(v___x_3164_, 4);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3164_, 1);
lean_dec(v_unused_3207_);
v___x_3170_ = v___x_3164_;
v_isShared_3171_ = v_isSharedCheck_3206_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_diag_3168_);
lean_inc(v_postponed_3167_);
lean_inc(v_zetaDeltaFVarIds_3166_);
lean_inc(v_mctx_3165_);
lean_dec(v___x_3164_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3206_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_mctx_3165_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_zetaDeltaFVarIds_3166_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_postponed_3167_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_diag_3168_);
v___x_3174_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v_r_3176_; 
v___x_3175_ = lean_st_ref_put(v___y_3136_, v___x_3174_);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3136_);
lean_inc_ref(v___y_3135_);
v_r_3176_ = lean_apply_5(v_x_3133_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
if (lean_obj_tag(v_r_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3193_; 
v_a_3177_ = lean_ctor_get(v_r_3176_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_r_3176_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3179_ = v_r_3176_;
v_isShared_3180_ = v_isSharedCheck_3193_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v_r_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3193_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
lean_inc(v_a_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 1);
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v___x_3183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3138_, v_isExporting_3145_, v___x_3160_, v___y_3136_, v___x_3172_, v___x_3182_);
lean_dec_ref(v___x_3182_);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___x_3183_, 0);
lean_dec(v_unused_3191_);
v___x_3185_ = v___x_3183_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v___x_3183_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_a_3177_);
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3177_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3194_ = lean_ctor_get(v_r_3176_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v_r_3176_, 1);
v___x_3195_ = lean_box(0);
v___x_3196_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3138_, v_isExporting_3145_, v___x_3160_, v___y_3136_, v___x_3172_, v___x_3195_);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3204_);
v___x_3198_ = v___x_3196_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v___x_3196_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 1);
lean_ctor_set(v___x_3198_, 0, v_a_3194_);
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3194_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3213_, lean_object* v_isExporting_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v_isExporting_boxed_3220_; lean_object* v_res_3221_; 
v_isExporting_boxed_3220_ = lean_unbox(v_isExporting_3214_);
v_res_3221_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3213_, v_isExporting_boxed_3220_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3222_, uint8_t v_when_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
if (v_when_3223_ == 0)
{
lean_object* v___x_3229_; 
lean_inc(v___y_3227_);
lean_inc_ref(v___y_3226_);
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
v___x_3229_ = lean_apply_5(v_x_3222_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, lean_box(0));
return v___x_3229_;
}
else
{
uint8_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = 0;
v___x_3231_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3222_, v___x_3230_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3232_, lean_object* v_when_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_when_boxed_3239_; lean_object* v_res_3240_; 
v_when_boxed_3239_ = lean_unbox(v_when_3233_);
v_res_3240_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3232_, v_when_boxed_3239_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3241_, lean_object* v_ext_3242_, uint8_t v_showInfo_3243_, uint8_t v_minIndexable_3244_, lean_object* v_attrName_3245_, lean_object* v_declName_3246_, lean_object* v_stx_3247_, uint8_t v_attrKind_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v___x_3279_; 
v___x_3252_ = 0;
v___x_3253_ = 1;
v___x_3254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3255_ = lean_unsigned_to_nat(32u);
v___x_3256_ = lean_mk_empty_array_with_capacity(v___x_3255_);
lean_dec_ref(v___x_3256_);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3261_ = lean_box(0);
lean_inc(v___x_3241_);
v___x_3262_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3262_, 0, v___x_3254_);
lean_ctor_set(v___x_3262_, 1, v___x_3241_);
lean_ctor_set(v___x_3262_, 2, v___x_3259_);
lean_ctor_set(v___x_3262_, 3, v___x_3260_);
lean_ctor_set(v___x_3262_, 4, v___x_3261_);
lean_ctor_set(v___x_3262_, 5, v___x_3257_);
lean_ctor_set(v___x_3262_, 6, v___x_3261_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7, v___x_3252_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 1, v___x_3252_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 2, v___x_3252_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*7 + 3, v___x_3253_);
v___x_3263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3263_);
lean_ctor_set(v___x_3266_, 1, v___x_3264_);
lean_ctor_set(v___x_3266_, 2, v___x_3241_);
lean_ctor_set(v___x_3266_, 3, v___x_3258_);
lean_ctor_set(v___x_3266_, 4, v___x_3265_);
v___x_3267_ = lean_st_mk_ref(v___x_3266_);
lean_inc(v_declName_3246_);
v___x_3279_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3246_, v___x_3252_, v___x_3262_, v___x_3267_, v___y_3249_, v___y_3250_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; 
lean_dec_ref_known(v___x_3279_, 1);
v___x_3280_ = lean_box(v_attrKind_3248_);
v___x_3281_ = lean_box(v_showInfo_3243_);
v___x_3282_ = lean_box(v_minIndexable_3244_);
v___x_3283_ = lean_box(v___x_3252_);
v___f_3284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3284_, 0, v_stx_3247_);
lean_closure_set(v___f_3284_, 1, v_ext_3242_);
lean_closure_set(v___f_3284_, 2, v_declName_3246_);
lean_closure_set(v___f_3284_, 3, v___x_3280_);
lean_closure_set(v___f_3284_, 4, v___x_3281_);
lean_closure_set(v___f_3284_, 5, v___x_3282_);
lean_closure_set(v___f_3284_, 6, v___x_3283_);
lean_closure_set(v___f_3284_, 7, v_attrName_3245_);
v___x_3285_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3284_, v___x_3253_, v___x_3262_, v___x_3267_, v___y_3249_, v___y_3250_);
lean_dec_ref_known(v___x_3262_, 7);
v___y_3269_ = v___x_3285_;
goto v___jp_3268_;
}
else
{
lean_dec_ref_known(v___x_3262_, 7);
lean_dec(v_stx_3247_);
lean_dec(v_declName_3246_);
lean_dec(v_attrName_3245_);
lean_dec_ref(v_ext_3242_);
v___y_3269_ = v___x_3279_;
goto v___jp_3268_;
}
v___jp_3268_:
{
if (lean_obj_tag(v___y_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
v_a_3270_ = lean_ctor_get(v___y_3269_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___y_3269_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3272_ = v___y_3269_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___y_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_st_ref_get(v___x_3267_);
lean_dec(v___x_3267_);
lean_dec(v___x_3274_);
if (v_isShared_3273_ == 0)
{
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3270_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
else
{
lean_dec(v___x_3267_);
return v___y_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3286_, lean_object* v_ext_3287_, lean_object* v_showInfo_3288_, lean_object* v_minIndexable_3289_, lean_object* v_attrName_3290_, lean_object* v_declName_3291_, lean_object* v_stx_3292_, lean_object* v_attrKind_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v_showInfo_boxed_3297_; uint8_t v_minIndexable_boxed_3298_; uint8_t v_attrKind_boxed_3299_; lean_object* v_res_3300_; 
v_showInfo_boxed_3297_ = lean_unbox(v_showInfo_3288_);
v_minIndexable_boxed_3298_ = lean_unbox(v_minIndexable_3289_);
v_attrKind_boxed_3299_ = lean_unbox(v_attrKind_3293_);
v_res_3300_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3286_, v_ext_3287_, v_showInfo_boxed_3297_, v_minIndexable_boxed_3298_, v_attrName_3290_, v_declName_3291_, v_stx_3292_, v_attrKind_boxed_3299_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3323_, uint8_t v_minIndexable_3324_, uint8_t v_showInfo_3325_, lean_object* v_ext_3326_, lean_object* v_ref_3327_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3380_; 
v___x_3329_ = lean_box(1);
v___x_3330_ = lean_box(v_showInfo_3325_);
lean_inc_n(v_attrName_3323_, 2);
lean_inc_ref(v_ext_3326_);
v___f_3331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3331_, 0, v___x_3329_);
lean_closure_set(v___f_3331_, 1, v_ext_3326_);
lean_closure_set(v___f_3331_, 2, v___x_3330_);
lean_closure_set(v___f_3331_, 3, v_attrName_3323_);
v___x_3332_ = lean_box(v_showInfo_3325_);
v___x_3333_ = lean_box(v_minIndexable_3324_);
v___f_3334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3334_, 0, v___x_3329_);
lean_closure_set(v___f_3334_, 1, v_ext_3326_);
lean_closure_set(v___f_3334_, 2, v___x_3332_);
lean_closure_set(v___f_3334_, 3, v___x_3333_);
lean_closure_set(v___f_3334_, 4, v_attrName_3323_);
if (v_minIndexable_3324_ == 0)
{
if (v_showInfo_3325_ == 0)
{
lean_inc(v_attrName_3323_);
v___y_3380_ = v_attrName_3323_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3323_);
v___x_3409_ = lean_name_append_after(v_attrName_3323_, v___x_3408_);
v___y_3380_ = v___x_3409_;
goto v___jp_3379_;
}
}
else
{
if (v_showInfo_3325_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3323_);
v___x_3411_ = lean_name_append_after(v_attrName_3323_, v___x_3410_);
v___y_3380_ = v___x_3411_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3323_);
v___x_3413_ = lean_name_append_after(v_attrName_3323_, v___x_3412_);
v___y_3380_ = v___x_3413_;
goto v___jp_3379_;
}
}
v___jp_3335_:
{
lean_object* v___x_3338_; uint8_t v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3339_ = 1;
v___x_3340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3323_, v___x_3339_);
v___x_3341_ = lean_string_append(v___x_3338_, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___x_3344_ = lean_string_append(v___x_3343_, v___x_3340_);
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
v___x_3347_ = lean_string_append(v___x_3346_, v___x_3340_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
v___x_3350_ = lean_string_append(v___x_3349_, v___x_3340_);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3352_ = lean_string_append(v___x_3350_, v___x_3351_);
v___x_3353_ = lean_string_append(v___x_3352_, v___x_3340_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3355_ = lean_string_append(v___x_3353_, v___x_3354_);
v___x_3356_ = lean_string_append(v___x_3355_, v___x_3340_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3358_ = lean_string_append(v___x_3356_, v___x_3357_);
v___x_3359_ = lean_string_append(v___x_3358_, v___x_3340_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
v___x_3362_ = lean_string_append(v___x_3361_, v___x_3340_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_string_append(v___x_3364_, v___x_3340_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3367_ = lean_string_append(v___x_3365_, v___x_3366_);
v___x_3368_ = lean_string_append(v___x_3367_, v___x_3340_);
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3370_ = lean_string_append(v___x_3368_, v___x_3369_);
v___x_3371_ = lean_string_append(v___x_3370_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3373_ = lean_string_append(v___x_3371_, v___x_3372_);
v___x_3374_ = lean_string_append(v___y_3337_, v___x_3373_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = 1;
v___x_3376_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3376_, 0, v_ref_3327_);
lean_ctor_set(v___x_3376_, 1, v___y_3336_);
lean_ctor_set(v___x_3376_, 2, v___x_3374_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*3, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v___f_3334_);
lean_ctor_set(v___x_3377_, 2, v___f_3331_);
v___x_3378_ = l_Lean_registerBuiltinAttribute(v___x_3377_);
return v___x_3378_;
}
v___jp_3379_:
{
if (v_minIndexable_3324_ == 0)
{
if (v_showInfo_3325_ == 0)
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3382_ = 1;
lean_inc(v_attrName_3323_);
v___x_3383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3323_, v___x_3382_);
v___x_3384_ = lean_string_append(v___x_3381_, v___x_3383_);
lean_dec_ref(v___x_3383_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
v___y_3336_ = v___y_3380_;
v___y_3337_ = v___x_3386_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3323_);
v___x_3388_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3323_, v_showInfo_3325_);
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_string_append(v___x_3391_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
v___y_3336_ = v___y_3380_;
v___y_3337_ = v___x_3394_;
goto v___jp_3335_;
}
}
else
{
if (v_showInfo_3325_ == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3323_);
v___x_3396_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3323_, v_minIndexable_3324_);
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
v___y_3336_ = v___y_3380_;
v___y_3337_ = v___x_3399_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3323_);
v___x_3401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3323_, v_showInfo_3325_);
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3404_ = lean_string_append(v___x_3402_, v___x_3403_);
v___x_3405_ = lean_string_append(v___x_3404_, v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
v___y_3336_ = v___y_3380_;
v___y_3337_ = v___x_3407_;
goto v___jp_3335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3414_, lean_object* v_minIndexable_3415_, lean_object* v_showInfo_3416_, lean_object* v_ext_3417_, lean_object* v_ref_3418_, lean_object* v_a_3419_){
_start:
{
uint8_t v_minIndexable_boxed_3420_; uint8_t v_showInfo_boxed_3421_; lean_object* v_res_3422_; 
v_minIndexable_boxed_3420_ = lean_unbox(v_minIndexable_3415_);
v_showInfo_boxed_3421_ = lean_unbox(v_showInfo_3416_);
v_res_3422_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3414_, v_minIndexable_boxed_3420_, v_showInfo_boxed_3421_, v_ext_3417_, v_ref_3418_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3423_, lean_object* v_msg_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3431_, lean_object* v_msg_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3431_, v_msg_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3439_, uint8_t v_attrKind_3440_, uint8_t v_showInfo_3441_, uint8_t v_minIndexable_3442_, lean_object* v_as_3443_, lean_object* v_as_x27_3444_, lean_object* v_b_3445_, lean_object* v_a_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3439_, v_attrKind_3440_, v_showInfo_3441_, v_minIndexable_3442_, v_as_x27_3444_, v_b_3445_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3453_, lean_object* v_attrKind_3454_, lean_object* v_showInfo_3455_, lean_object* v_minIndexable_3456_, lean_object* v_as_3457_, lean_object* v_as_x27_3458_, lean_object* v_b_3459_, lean_object* v_a_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v_attrKind_boxed_3466_; uint8_t v_showInfo_boxed_3467_; uint8_t v_minIndexable_boxed_3468_; lean_object* v_res_3469_; 
v_attrKind_boxed_3466_ = lean_unbox(v_attrKind_3454_);
v_showInfo_boxed_3467_ = lean_unbox(v_showInfo_3455_);
v_minIndexable_boxed_3468_ = lean_unbox(v_minIndexable_3456_);
v_res_3469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3453_, v_attrKind_boxed_3466_, v_showInfo_boxed_3467_, v_minIndexable_boxed_3468_, v_as_3457_, v_as_x27_3458_, v_b_3459_, v_a_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v_as_x27_3458_);
lean_dec(v_as_3457_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3470_, lean_object* v_x_3471_, uint8_t v_isExporting_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3471_, v_isExporting_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_x_3480_, lean_object* v_isExporting_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v_isExporting_boxed_3487_; lean_object* v_res_3488_; 
v_isExporting_boxed_3487_ = lean_unbox(v_isExporting_3481_);
v_res_3488_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3479_, v_x_3480_, v_isExporting_boxed_3487_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3489_, lean_object* v_x_3490_, uint8_t v_when_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3490_, v_when_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3498_, lean_object* v_x_3499_, lean_object* v_when_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v_when_boxed_3506_; lean_object* v_res_3507_; 
v_when_boxed_3506_ = lean_unbox(v_when_3500_);
v_res_3507_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3498_, v_x_3499_, v_when_boxed_3506_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3508_, lean_object* v_m_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3509_, v_a_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3512_, lean_object* v_m_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3512_, v_m_3513_, v_a_3514_);
lean_dec(v_a_3514_);
lean_dec_ref(v_m_3513_);
return v_res_3515_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3516_, lean_object* v_x_3517_, lean_object* v_x_3518_){
_start:
{
uint8_t v___x_3519_; 
v___x_3519_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3517_, v_x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_){
_start:
{
uint8_t v_res_3523_; lean_object* v_r_3524_; 
v_res_3523_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3520_, v_x_3521_, v_x_3522_);
lean_dec_ref(v_x_3522_);
lean_dec_ref(v_x_3521_);
v_r_3524_ = lean_box(v_res_3523_);
return v_r_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3525_, lean_object* v_a_3526_, lean_object* v_x_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3526_, v_x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3529_, lean_object* v_a_3530_, lean_object* v_x_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3529_, v_a_3530_, v_x_3531_);
lean_dec(v_x_3531_);
lean_dec(v_a_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3533_, lean_object* v_x_3534_, size_t v_x_3535_, lean_object* v_x_3536_){
_start:
{
uint8_t v___x_3537_; 
v___x_3537_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3534_, v_x_3535_, v_x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_){
_start:
{
size_t v_x_16835__boxed_3542_; uint8_t v_res_3543_; lean_object* v_r_3544_; 
v_x_16835__boxed_3542_ = lean_unbox_usize(v_x_3540_);
lean_dec(v_x_3540_);
v_res_3543_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3538_, v_x_3539_, v_x_16835__boxed_3542_, v_x_3541_);
lean_dec_ref(v_x_3541_);
lean_dec_ref(v_x_3539_);
v_r_3544_ = lean_box(v_res_3543_);
return v_r_3544_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3545_, lean_object* v_keys_3546_, lean_object* v_vals_3547_, lean_object* v_heq_3548_, lean_object* v_i_3549_, lean_object* v_k_3550_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3546_, v_i_3549_, v_k_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3552_, lean_object* v_keys_3553_, lean_object* v_vals_3554_, lean_object* v_heq_3555_, lean_object* v_i_3556_, lean_object* v_k_3557_){
_start:
{
uint8_t v_res_3558_; lean_object* v_r_3559_; 
v_res_3558_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3552_, v_keys_3553_, v_vals_3554_, v_heq_3555_, v_i_3556_, v_k_3557_);
lean_dec_ref(v_k_3557_);
lean_dec_ref(v_vals_3554_);
lean_dec_ref(v_keys_3553_);
v_r_3559_ = lean_box(v_res_3558_);
return v_r_3559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = lean_unsigned_to_nat(16u);
v___x_3562_ = lean_mk_array(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3564_ = lean_unsigned_to_nat(0u);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v___x_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3568_ = lean_st_mk_ref(v___x_3567_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3572_, lean_object* v_msg_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_ref_3577_; lean_object* v___x_3578_; lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3623_; 
v_ref_3577_ = lean_ctor_get(v___y_3574_, 2);
v___x_3578_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3573_, v___y_3574_, v___y_3575_);
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3623_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3623_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v_traceState_3584_; lean_object* v_env_3585_; lean_object* v_nextMacroScope_3586_; lean_object* v_ngen_3587_; lean_object* v_auxDeclNGen_3588_; lean_object* v_cache_3589_; lean_object* v_messages_3590_; lean_object* v_infoState_3591_; lean_object* v_snapshotTasks_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3622_; 
v___x_3583_ = lean_st_ref_take(v___y_3575_);
v_traceState_3584_ = lean_ctor_get(v___x_3583_, 4);
v_env_3585_ = lean_ctor_get(v___x_3583_, 0);
v_nextMacroScope_3586_ = lean_ctor_get(v___x_3583_, 1);
v_ngen_3587_ = lean_ctor_get(v___x_3583_, 2);
v_auxDeclNGen_3588_ = lean_ctor_get(v___x_3583_, 3);
v_cache_3589_ = lean_ctor_get(v___x_3583_, 5);
v_messages_3590_ = lean_ctor_get(v___x_3583_, 6);
v_infoState_3591_ = lean_ctor_get(v___x_3583_, 7);
v_snapshotTasks_3592_ = lean_ctor_get(v___x_3583_, 8);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3594_ = v___x_3583_;
v_isShared_3595_ = v_isSharedCheck_3622_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_snapshotTasks_3592_);
lean_inc(v_infoState_3591_);
lean_inc(v_messages_3590_);
lean_inc(v_cache_3589_);
lean_inc(v_traceState_3584_);
lean_inc(v_auxDeclNGen_3588_);
lean_inc(v_ngen_3587_);
lean_inc(v_nextMacroScope_3586_);
lean_inc(v_env_3585_);
lean_dec(v___x_3583_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3622_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
uint64_t v_tid_3596_; lean_object* v_traces_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3621_; 
v_tid_3596_ = lean_ctor_get_uint64(v_traceState_3584_, sizeof(void*)*1);
v_traces_3597_ = lean_ctor_get(v_traceState_3584_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_traceState_3584_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3599_ = v_traceState_3584_;
v_isShared_3600_ = v_isSharedCheck_3621_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_traces_3597_);
lean_dec(v_traceState_3584_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3621_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; double v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3601_ = lean_box(0);
v___x_3602_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3603_ = 0;
v___x_3604_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3605_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3605_, 0, v_cls_3572_);
lean_ctor_set(v___x_3605_, 1, v___x_3601_);
lean_ctor_set(v___x_3605_, 2, v___x_3604_);
lean_ctor_set_float(v___x_3605_, sizeof(void*)*3, v___x_3602_);
lean_ctor_set_float(v___x_3605_, sizeof(void*)*3 + 8, v___x_3602_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*3 + 16, v___x_3603_);
v___x_3606_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3607_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v_a_3579_);
lean_ctor_set(v___x_3607_, 2, v___x_3606_);
lean_inc(v_ref_3577_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_ref_3577_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_PersistentArray_push___redArg(v_traces_3597_, v___x_3608_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3609_);
v___x_3611_ = v___x_3599_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3609_);
lean_ctor_set_uint64(v_reuseFailAlloc_3620_, sizeof(void*)*1, v_tid_3596_);
v___x_3611_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v___x_3611_);
v___x_3613_ = v___x_3594_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_env_3585_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_nextMacroScope_3586_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_ngen_3587_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_auxDeclNGen_3588_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_cache_3589_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_messages_3590_);
lean_ctor_set(v_reuseFailAlloc_3619_, 7, v_infoState_3591_);
lean_ctor_set(v_reuseFailAlloc_3619_, 8, v_snapshotTasks_3592_);
v___x_3613_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3614_ = lean_st_ref_put(v___y_3575_, v___x_3613_);
v___x_3615_ = lean_box(0);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3615_);
v___x_3617_ = v___x_3581_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3624_, lean_object* v_msg_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3624_, v_msg_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3630_, uint8_t v_isMeta_3631_, lean_object* v_hint_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v_env_3637_; uint8_t v_isExporting_3638_; lean_object* v___x_3639_; lean_object* v_env_3640_; lean_object* v___x_3641_; lean_object* v_entry_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___y_3647_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3636_ = lean_st_ref_get(v___y_3634_);
v_env_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc_ref(v_env_3637_);
lean_dec(v___x_3636_);
v_isExporting_3638_ = lean_ctor_get_uint8(v_env_3637_, sizeof(void*)*8);
lean_dec_ref(v_env_3637_);
v___x_3639_ = lean_st_ref_get(v___y_3634_);
v_env_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc_ref(v_env_3640_);
lean_dec(v___x_3639_);
v___x_3641_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3630_);
v_entry_3642_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3642_, 0, v_mod_3630_);
lean_ctor_set_uint8(v_entry_3642_, sizeof(void*)*1, v_isExporting_3638_);
lean_ctor_set_uint8(v_entry_3642_, sizeof(void*)*1 + 1, v_isMeta_3631_);
v___x_3643_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3644_ = lean_box(1);
v___x_3645_ = lean_box(0);
v___x_3672_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3641_, v___x_3643_, v_env_3640_, v___x_3644_, v___x_3645_);
v___x_3673_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3672_, v_entry_3642_);
lean_dec(v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v_toCold_3674_; lean_object* v_options_3675_; uint8_t v_hasTrace_3676_; 
v_toCold_3674_ = lean_ctor_get(v___y_3633_, 0);
v_options_3675_ = lean_ctor_get(v_toCold_3674_, 2);
v_hasTrace_3676_ = lean_ctor_get_uint8(v_options_3675_, sizeof(void*)*1);
if (v_hasTrace_3676_ == 0)
{
lean_dec(v_hint_3632_);
lean_dec(v_mod_3630_);
v___y_3647_ = v___y_3634_;
goto v___jp_3646_;
}
else
{
lean_object* v_inheritedTraceOptions_3677_; lean_object* v_cls_3678_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_inheritedTraceOptions_3677_ = lean_ctor_get(v_toCold_3674_, 11);
v_cls_3678_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3698_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3677_, v_options_3675_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_dec(v_hint_3632_);
lean_dec(v_mod_3630_);
v___y_3647_ = v___y_3634_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3700_; lean_object* v___y_3702_; 
v___x_3700_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3638_ == 0)
{
lean_object* v___x_3709_; 
v___x_3709_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3702_ = v___x_3709_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3710_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3702_ = v___x_3710_;
goto v___jp_3701_;
}
v___jp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_inc_ref(v___y_3702_);
v___x_3703_ = l_Lean_stringToMessageData(v___y_3702_);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3700_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
if (v_isMeta_3631_ == 0)
{
lean_object* v___x_3707_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3685_ = v___x_3706_;
v___y_3686_ = v___x_3707_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3708_; 
v___x_3708_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3685_ = v___x_3706_;
v___y_3686_ = v___x_3708_;
goto v___jp_3684_;
}
}
}
v___jp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___y_3680_);
lean_ctor_set(v___x_3682_, 1, v___y_3681_);
v___x_3683_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3678_, v___x_3682_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_dec_ref_known(v___x_3683_, 1);
v___y_3647_ = v___y_3634_;
goto v___jp_3646_;
}
else
{
lean_dec_ref_known(v_entry_3642_, 1);
return v___x_3683_;
}
}
v___jp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
lean_inc_ref(v___y_3686_);
v___x_3687_ = l_Lean_stringToMessageData(v___y_3686_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___y_3685_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_Lean_MessageData_ofName(v_mod_3630_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = l_Lean_Name_isAnonymous(v_hint_3632_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3695_ = l_Lean_MessageData_ofName(v_hint_3632_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___y_3680_ = v___x_3692_;
v___y_3681_ = v___x_3696_;
goto v___jp_3679_;
}
else
{
lean_object* v___x_3697_; 
lean_dec(v_hint_3632_);
v___x_3697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3680_ = v___x_3692_;
v___y_3681_ = v___x_3697_;
goto v___jp_3679_;
}
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec_ref_known(v_entry_3642_, 1);
lean_dec(v_hint_3632_);
lean_dec(v_mod_3630_);
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
v___jp_3646_:
{
lean_object* v___x_3648_; lean_object* v_toEnvExtension_3649_; lean_object* v_env_3650_; lean_object* v_nextMacroScope_3651_; lean_object* v_ngen_3652_; lean_object* v_auxDeclNGen_3653_; lean_object* v_traceState_3654_; lean_object* v_messages_3655_; lean_object* v_infoState_3656_; lean_object* v_snapshotTasks_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3670_; 
v___x_3648_ = lean_st_ref_take(v___y_3647_);
v_toEnvExtension_3649_ = lean_ctor_get(v___x_3643_, 0);
v_env_3650_ = lean_ctor_get(v___x_3648_, 0);
v_nextMacroScope_3651_ = lean_ctor_get(v___x_3648_, 1);
v_ngen_3652_ = lean_ctor_get(v___x_3648_, 2);
v_auxDeclNGen_3653_ = lean_ctor_get(v___x_3648_, 3);
v_traceState_3654_ = lean_ctor_get(v___x_3648_, 4);
v_messages_3655_ = lean_ctor_get(v___x_3648_, 6);
v_infoState_3656_ = lean_ctor_get(v___x_3648_, 7);
v_snapshotTasks_3657_ = lean_ctor_get(v___x_3648_, 8);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___x_3648_, 5);
lean_dec(v_unused_3671_);
v___x_3659_ = v___x_3648_;
v_isShared_3660_ = v_isSharedCheck_3670_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_snapshotTasks_3657_);
lean_inc(v_infoState_3656_);
lean_inc(v_messages_3655_);
lean_inc(v_traceState_3654_);
lean_inc(v_auxDeclNGen_3653_);
lean_inc(v_ngen_3652_);
lean_inc(v_nextMacroScope_3651_);
lean_inc(v_env_3650_);
lean_dec(v___x_3648_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3670_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v_asyncMode_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v_asyncMode_3661_ = lean_ctor_get(v_toEnvExtension_3649_, 2);
v___x_3662_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3643_, v_env_3650_, v_entry_3642_, v_asyncMode_3661_, v___x_3645_);
v___x_3663_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 5, v___x_3663_);
lean_ctor_set(v___x_3659_, 0, v___x_3662_);
v___x_3665_ = v___x_3659_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_nextMacroScope_3651_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_ngen_3652_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_auxDeclNGen_3653_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_traceState_3654_);
lean_ctor_set(v_reuseFailAlloc_3669_, 5, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3669_, 6, v_messages_3655_);
lean_ctor_set(v_reuseFailAlloc_3669_, 7, v_infoState_3656_);
lean_ctor_set(v_reuseFailAlloc_3669_, 8, v_snapshotTasks_3657_);
v___x_3665_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_st_ref_put(v___y_3647_, v___x_3665_);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3713_, lean_object* v_isMeta_3714_, lean_object* v_hint_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v_isMeta_boxed_3719_; lean_object* v_res_3720_; 
v_isMeta_boxed_3719_ = lean_unbox(v_isMeta_3714_);
v_res_3720_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3713_, v_isMeta_boxed_3719_, v_hint_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3721_, lean_object* v_declName_3722_, lean_object* v_as_3723_, size_t v_sz_3724_, size_t v_i_3725_, lean_object* v_b_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_usize_dec_lt(v_i_3725_, v_sz_3724_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
lean_dec(v_declName_3722_);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_b_3726_);
return v___x_3731_;
}
else
{
lean_object* v___x_3732_; lean_object* v_modules_3733_; lean_object* v___x_3734_; lean_object* v_a_3735_; lean_object* v___x_3736_; lean_object* v_toImport_3737_; lean_object* v_module_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; 
v___x_3732_ = l_Lean_Environment_header(v___x_3721_);
v_modules_3733_ = lean_ctor_get(v___x_3732_, 3);
lean_inc_ref(v_modules_3733_);
lean_dec_ref(v___x_3732_);
v___x_3734_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3735_ = lean_array_uget_borrowed(v_as_3723_, v_i_3725_);
v___x_3736_ = lean_array_get(v___x_3734_, v_modules_3733_, v_a_3735_);
lean_dec_ref(v_modules_3733_);
v_toImport_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc_ref(v_toImport_3737_);
lean_dec(v___x_3736_);
v_module_3738_ = lean_ctor_get(v_toImport_3737_, 0);
lean_inc(v_module_3738_);
lean_dec_ref(v_toImport_3737_);
v___x_3739_ = 0;
lean_inc(v_declName_3722_);
v___x_3740_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3738_, v___x_3739_, v_declName_3722_, v___y_3727_, v___y_3728_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; 
lean_dec_ref_known(v___x_3740_, 1);
v___x_3741_ = lean_box(0);
v___x_3742_ = ((size_t)1ULL);
v___x_3743_ = lean_usize_add(v_i_3725_, v___x_3742_);
v_i_3725_ = v___x_3743_;
v_b_3726_ = v___x_3741_;
goto _start;
}
else
{
lean_dec(v_declName_3722_);
return v___x_3740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3745_, lean_object* v_declName_3746_, lean_object* v_as_3747_, lean_object* v_sz_3748_, lean_object* v_i_3749_, lean_object* v_b_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3748_);
lean_dec(v_sz_3748_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3749_);
lean_dec(v_i_3749_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3745_, v_declName_3746_, v_as_3747_, v_sz_boxed_3754_, v_i_boxed_3755_, v_b_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec_ref(v_as_3747_);
lean_dec_ref(v___x_3745_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3757_, uint8_t v_isMeta_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v_env_3766_; lean_object* v___y_3768_; lean_object* v___x_3781_; 
v___x_3762_ = lean_st_ref_get(v___y_3760_);
v_env_3766_ = lean_ctor_get(v___x_3762_, 0);
lean_inc_ref(v_env_3766_);
lean_dec(v___x_3762_);
v___x_3781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3766_, v_declName_3757_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3757_);
goto v___jp_3763_;
}
else
{
lean_object* v_val_3782_; lean_object* v___x_3783_; lean_object* v_modules_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v_val_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = l_Lean_Environment_header(v_env_3766_);
v_modules_3784_ = lean_ctor_get(v___x_3783_, 3);
lean_inc_ref(v_modules_3784_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = lean_array_get_size(v_modules_3784_);
v___x_3786_ = lean_nat_dec_lt(v_val_3782_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_dec_ref(v_modules_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3757_);
goto v___jp_3763_;
}
else
{
lean_object* v___x_3787_; lean_object* v_env_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___y_3792_; 
v___x_3787_ = lean_st_ref_get(v___y_3760_);
v_env_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc_ref(v_env_3788_);
lean_dec(v___x_3787_);
v___x_3789_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3790_ = lean_array_fget(v_modules_3784_, v_val_3782_);
lean_dec(v_val_3782_);
lean_dec_ref(v_modules_3784_);
if (v_isMeta_3758_ == 0)
{
lean_dec_ref(v_env_3788_);
v___y_3792_ = v_isMeta_3758_;
goto v___jp_3791_;
}
else
{
uint8_t v___x_3803_; 
lean_inc(v_declName_3757_);
v___x_3803_ = l_Lean_isMarkedMeta(v_env_3788_, v_declName_3757_);
if (v___x_3803_ == 0)
{
v___y_3792_ = v_isMeta_3758_;
goto v___jp_3791_;
}
else
{
uint8_t v___x_3804_; 
v___x_3804_ = 0;
v___y_3792_ = v___x_3804_;
goto v___jp_3791_;
}
}
v___jp_3791_:
{
lean_object* v_toImport_3793_; lean_object* v_module_3794_; lean_object* v___x_3795_; 
v_toImport_3793_ = lean_ctor_get(v___x_3790_, 0);
lean_inc_ref(v_toImport_3793_);
lean_dec(v___x_3790_);
v_module_3794_ = lean_ctor_get(v_toImport_3793_, 0);
lean_inc(v_module_3794_);
lean_dec_ref(v_toImport_3793_);
lean_inc(v_declName_3757_);
v___x_3795_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3794_, v___y_3792_, v_declName_3757_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_dec_ref_known(v___x_3795_, 1);
v___x_3796_ = l_Lean_indirectModUseExt;
v___x_3797_ = lean_box(1);
v___x_3798_ = lean_box(0);
lean_inc_ref(v_env_3766_);
v___x_3799_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3789_, v___x_3796_, v_env_3766_, v___x_3797_, v___x_3798_);
v___x_3800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3799_, v_declName_3757_);
lean_dec(v___x_3799_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3801_; 
v___x_3801_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3768_ = v___x_3801_;
goto v___jp_3767_;
}
else
{
lean_object* v_val_3802_; 
v_val_3802_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___x_3800_, 1);
v___y_3768_ = v_val_3802_;
goto v___jp_3767_;
}
}
else
{
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3757_);
return v___x_3795_;
}
}
}
}
v___jp_3763_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
return v___x_3765_;
}
v___jp_3767_:
{
lean_object* v___x_3769_; size_t v_sz_3770_; size_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3769_ = lean_box(0);
v_sz_3770_ = lean_array_size(v___y_3768_);
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3766_, v_declName_3757_, v___y_3768_, v_sz_3770_, v___x_3771_, v___x_3769_, v___y_3759_, v___y_3760_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_env_3766_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v___x_3772_, 0);
lean_dec(v_unused_3780_);
v___x_3774_ = v___x_3772_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v___x_3772_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3769_);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3769_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
else
{
return v___x_3772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3805_, lean_object* v_isMeta_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
uint8_t v_isMeta_boxed_3810_; lean_object* v_res_3811_; 
v_isMeta_boxed_3810_ = lean_unbox(v_isMeta_3806_);
v_res_3811_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3805_, v_isMeta_boxed_3810_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3817_ = lean_st_ref_get(v___x_3816_);
v___x_3818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3817_, v_attrName_3812_);
lean_dec(v___x_3817_);
if (lean_obj_tag(v___x_3818_) == 1)
{
lean_object* v_val_3819_; lean_object* v_ext_3820_; lean_object* v_name_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; 
v_val_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_val_3819_);
v_ext_3820_ = lean_ctor_get(v_val_3819_, 1);
lean_inc_ref(v_ext_3820_);
lean_dec(v_val_3819_);
v_name_3821_ = lean_ctor_get(v_ext_3820_, 1);
lean_inc(v_name_3821_);
lean_dec_ref(v_ext_3820_);
v___x_3822_ = 1;
v___x_3823_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3821_, v___x_3822_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v___x_3823_, 0);
lean_dec(v_unused_3831_);
v___x_3825_ = v___x_3823_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v___x_3823_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3818_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3818_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref_known(v___x_3818_, 1);
v_a_3832_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3823_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3823_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3818_);
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3841_, v_a_3842_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_attrName_3841_);
return v_res_3845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
return v_x_3847_;
}
else
{
lean_object* v_key_3849_; lean_object* v_value_3850_; lean_object* v_tail_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3877_; 
v_key_3849_ = lean_ctor_get(v_x_3848_, 0);
v_value_3850_ = lean_ctor_get(v_x_3848_, 1);
v_tail_3851_ = lean_ctor_get(v_x_3848_, 2);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3853_ = v_x_3848_;
v_isShared_3854_ = v_isSharedCheck_3877_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_tail_3851_);
lean_inc(v_value_3850_);
lean_inc(v_key_3849_);
lean_dec(v_x_3848_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3877_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; uint64_t v___y_3857_; 
v___x_3855_ = lean_array_get_size(v_x_3847_);
if (lean_obj_tag(v_key_3849_) == 0)
{
uint64_t v___x_3875_; 
v___x_3875_ = 1723ULL;
v___y_3857_ = v___x_3875_;
goto v___jp_3856_;
}
else
{
uint64_t v_hash_3876_; 
v_hash_3876_ = lean_ctor_get_uint64(v_key_3849_, sizeof(void*)*2);
v___y_3857_ = v_hash_3876_;
goto v___jp_3856_;
}
v___jp_3856_:
{
uint64_t v___x_3858_; uint64_t v___x_3859_; uint64_t v_fold_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; uint64_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3858_ = 32ULL;
v___x_3859_ = lean_uint64_shift_right(v___y_3857_, v___x_3858_);
v_fold_3860_ = lean_uint64_xor(v___y_3857_, v___x_3859_);
v___x_3861_ = 16ULL;
v___x_3862_ = lean_uint64_shift_right(v_fold_3860_, v___x_3861_);
v___x_3863_ = lean_uint64_xor(v_fold_3860_, v___x_3862_);
v___x_3864_ = lean_uint64_to_usize(v___x_3863_);
v___x_3865_ = lean_usize_of_nat(v___x_3855_);
v___x_3866_ = ((size_t)1ULL);
v___x_3867_ = lean_usize_sub(v___x_3865_, v___x_3866_);
v___x_3868_ = lean_usize_land(v___x_3864_, v___x_3867_);
v___x_3869_ = lean_array_uget_borrowed(v_x_3847_, v___x_3868_);
lean_inc(v___x_3869_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 2, v___x_3869_);
v___x_3871_ = v___x_3853_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_key_3849_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_value_3850_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_array_uset(v_x_3847_, v___x_3868_, v___x_3871_);
v_x_3847_ = v___x_3872_;
v_x_3848_ = v_tail_3851_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3878_, lean_object* v_source_3879_, lean_object* v_target_3880_){
_start:
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = lean_array_get_size(v_source_3879_);
v___x_3882_ = lean_nat_dec_lt(v_i_3878_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_dec_ref(v_source_3879_);
lean_dec(v_i_3878_);
return v_target_3880_;
}
else
{
lean_object* v_es_3883_; lean_object* v___x_3884_; lean_object* v_source_3885_; lean_object* v_target_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_es_3883_ = lean_array_fget(v_source_3879_, v_i_3878_);
v___x_3884_ = lean_box(0);
v_source_3885_ = lean_array_fset(v_source_3879_, v_i_3878_, v___x_3884_);
v_target_3886_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3880_, v_es_3883_);
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = lean_nat_add(v_i_3878_, v___x_3887_);
lean_dec(v_i_3878_);
v_i_3878_ = v___x_3888_;
v_source_3879_ = v_source_3885_;
v_target_3880_ = v_target_3886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3890_){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_nbuckets_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3891_ = lean_array_get_size(v_data_3890_);
v___x_3892_ = lean_unsigned_to_nat(2u);
v_nbuckets_3893_ = lean_nat_mul(v___x_3891_, v___x_3892_);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_mk_array(v_nbuckets_3893_, v___x_3895_);
v___x_3897_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3894_, v_data_3890_, v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 0)
{
uint8_t v___x_3900_; 
v___x_3900_ = 0;
return v___x_3900_;
}
else
{
lean_object* v_key_3901_; lean_object* v_tail_3902_; uint8_t v___x_3903_; 
v_key_3901_ = lean_ctor_get(v_x_3899_, 0);
v_tail_3902_ = lean_ctor_get(v_x_3899_, 2);
v___x_3903_ = lean_name_eq(v_key_3901_, v_a_3898_);
if (v___x_3903_ == 0)
{
v_x_3899_ = v_tail_3902_;
goto _start;
}
else
{
return v___x_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3905_, lean_object* v_x_3906_){
_start:
{
uint8_t v_res_3907_; lean_object* v_r_3908_; 
v_res_3907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3905_, v_x_3906_);
lean_dec(v_x_3906_);
lean_dec(v_a_3905_);
v_r_3908_ = lean_box(v_res_3907_);
return v_r_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3909_, lean_object* v_b_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_dec(v_b_3910_);
lean_dec(v_a_3909_);
return v_x_3911_;
}
else
{
lean_object* v_key_3912_; lean_object* v_value_3913_; lean_object* v_tail_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3926_; 
v_key_3912_ = lean_ctor_get(v_x_3911_, 0);
v_value_3913_ = lean_ctor_get(v_x_3911_, 1);
v_tail_3914_ = lean_ctor_get(v_x_3911_, 2);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3911_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3916_ = v_x_3911_;
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_tail_3914_);
lean_inc(v_value_3913_);
lean_inc(v_key_3912_);
lean_dec(v_x_3911_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_name_eq(v_key_3912_, v_a_3909_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3909_, v_b_3910_, v_tail_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 2, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_key_3912_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_value_3913_);
lean_ctor_set(v_reuseFailAlloc_3922_, 2, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_value_3913_);
lean_dec(v_key_3912_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v_b_3910_);
lean_ctor_set(v___x_3916_, 0, v_a_3909_);
v___x_3924_ = v___x_3916_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3909_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_b_3910_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_tail_3914_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3927_, lean_object* v_a_3928_, lean_object* v_b_3929_){
_start:
{
lean_object* v_size_3930_; lean_object* v_buckets_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3977_; 
v_size_3930_ = lean_ctor_get(v_m_3927_, 0);
v_buckets_3931_ = lean_ctor_get(v_m_3927_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_m_3927_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3933_ = v_m_3927_;
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_buckets_3931_);
lean_inc(v_size_3930_);
lean_dec(v_m_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; uint64_t v___y_3937_; 
v___x_3935_ = lean_array_get_size(v_buckets_3931_);
if (lean_obj_tag(v_a_3928_) == 0)
{
uint64_t v___x_3975_; 
v___x_3975_ = 1723ULL;
v___y_3937_ = v___x_3975_;
goto v___jp_3936_;
}
else
{
uint64_t v_hash_3976_; 
v_hash_3976_ = lean_ctor_get_uint64(v_a_3928_, sizeof(void*)*2);
v___y_3937_ = v_hash_3976_;
goto v___jp_3936_;
}
v___jp_3936_:
{
uint64_t v___x_3938_; uint64_t v___x_3939_; uint64_t v_fold_3940_; uint64_t v___x_3941_; uint64_t v___x_3942_; uint64_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; size_t v___x_3948_; lean_object* v_bkt_3949_; uint8_t v___x_3950_; 
v___x_3938_ = 32ULL;
v___x_3939_ = lean_uint64_shift_right(v___y_3937_, v___x_3938_);
v_fold_3940_ = lean_uint64_xor(v___y_3937_, v___x_3939_);
v___x_3941_ = 16ULL;
v___x_3942_ = lean_uint64_shift_right(v_fold_3940_, v___x_3941_);
v___x_3943_ = lean_uint64_xor(v_fold_3940_, v___x_3942_);
v___x_3944_ = lean_uint64_to_usize(v___x_3943_);
v___x_3945_ = lean_usize_of_nat(v___x_3935_);
v___x_3946_ = ((size_t)1ULL);
v___x_3947_ = lean_usize_sub(v___x_3945_, v___x_3946_);
v___x_3948_ = lean_usize_land(v___x_3944_, v___x_3947_);
v_bkt_3949_ = lean_array_uget_borrowed(v_buckets_3931_, v___x_3948_);
v___x_3950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3928_, v_bkt_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v_size_x27_3952_; lean_object* v___x_3953_; lean_object* v_buckets_x27_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
v_size_x27_3952_ = lean_nat_add(v_size_3930_, v___x_3951_);
lean_dec(v_size_3930_);
lean_inc(v_bkt_3949_);
v___x_3953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3953_, 0, v_a_3928_);
lean_ctor_set(v___x_3953_, 1, v_b_3929_);
lean_ctor_set(v___x_3953_, 2, v_bkt_3949_);
v_buckets_x27_3954_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3953_);
v___x_3955_ = lean_unsigned_to_nat(4u);
v___x_3956_ = lean_nat_mul(v_size_x27_3952_, v___x_3955_);
v___x_3957_ = lean_unsigned_to_nat(3u);
v___x_3958_ = lean_nat_div(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_array_get_size(v_buckets_x27_3954_);
v___x_3960_ = lean_nat_dec_le(v___x_3958_, v___x_3959_);
lean_dec(v___x_3958_);
if (v___x_3960_ == 0)
{
lean_object* v_val_3961_; lean_object* v___x_3963_; 
v_val_3961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3954_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_val_3961_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3963_ = v___x_3933_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_val_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
else
{
lean_object* v___x_3966_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_buckets_x27_3954_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3966_ = v___x_3933_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_buckets_x27_3954_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v_buckets_x27_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
lean_inc(v_bkt_3949_);
v___x_3968_ = lean_box(0);
v_buckets_x27_3969_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3968_);
v___x_3970_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3928_, v_b_3929_, v_bkt_3949_);
v___x_3971_ = lean_array_uset(v_buckets_x27_3969_, v___x_3948_, v___x_3970_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v___x_3971_);
v___x_3973_ = v___x_3933_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_size_3930_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3978_, lean_object* v_ref_3979_){
_start:
{
lean_object* v___x_3981_; 
lean_inc(v_ref_3979_);
v___x_3981_ = l_Lean_Meta_Grind_mkExtension(v_ref_3979_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc_n(v_a_3982_, 2);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = 0;
v___x_3984_ = 1;
lean_inc(v_ref_3979_);
lean_inc(v_attrName_3978_);
v___x_3985_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref_known(v___x_3985_, 1);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3986_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref_known(v___x_3986_, 1);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3987_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref_known(v___x_3987_, 1);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3988_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3999_; 
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3988_, 0);
lean_dec(v_unused_4000_);
v___x_3990_ = v___x_3988_;
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3992_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3993_ = lean_st_ref_take(v___x_3992_);
lean_inc(v_a_3982_);
v___x_3994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3993_, v_attrName_3978_, v_a_3982_);
v___x_3995_ = lean_st_ref_put(v___x_3992_, v___x_3994_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v_a_3982_);
v___x_3997_ = v___x_3990_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3982_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_a_3982_);
lean_dec(v_attrName_3978_);
v_a_4001_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3988_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3988_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4009_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3987_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3987_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4017_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3986_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3986_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4025_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_3985_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_3985_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
return v___x_3981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4033_, lean_object* v_ref_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4033_, v_ref_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4037_, lean_object* v_m_4038_, lean_object* v_a_4039_, lean_object* v_b_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4038_, v_a_4039_, v_b_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4042_, lean_object* v_a_4043_, lean_object* v_x_4044_){
_start:
{
uint8_t v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_a_4047_, lean_object* v_x_4048_){
_start:
{
uint8_t v_res_4049_; lean_object* v_r_4050_; 
v_res_4049_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4046_, v_a_4047_, v_x_4048_);
lean_dec(v_x_4048_);
lean_dec(v_a_4047_);
v_r_4050_ = lean_box(v_res_4049_);
return v_r_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4051_, lean_object* v_data_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4054_, lean_object* v_a_4055_, lean_object* v_b_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4055_, v_b_4056_, v_x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4059_, lean_object* v_i_4060_, lean_object* v_source_4061_, lean_object* v_target_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4060_, v_source_4061_, v_target_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4076_ = l_Lean_Meta_Grind_registerAttr(v___x_4074_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4091_ = l_Lean_Meta_Grind_registerAttr(v___x_4089_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v___x_4097_; lean_object* v_env_4098_; lean_object* v___x_4099_; lean_object* v_ext_4100_; lean_object* v_toEnvExtension_4101_; lean_object* v_asyncMode_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_casesTypes_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4097_ = lean_st_ref_get(v_a_4095_);
v_env_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_ref(v_env_4098_);
lean_dec(v___x_4097_);
v___x_4099_ = l_Lean_Meta_Grind_grindExt;
v_ext_4100_ = lean_ctor_get(v___x_4099_, 1);
v_toEnvExtension_4101_ = lean_ctor_get(v_ext_4100_, 0);
v_asyncMode_4102_ = lean_ctor_get(v_toEnvExtension_4101_, 2);
v___x_4103_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4104_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4103_, v___x_4099_, v_env_4098_, v_asyncMode_4102_);
v_casesTypes_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc_ref(v_casesTypes_4105_);
lean_dec(v___x_4104_);
v___x_4106_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4105_, v_declName_4094_);
lean_dec_ref(v_casesTypes_4105_);
v___x_4107_ = lean_box(v___x_4106_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec(v_declName_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4113_, v_a_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_declName_4118_);
return v_res_4122_;
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
