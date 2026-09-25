// Lean compiler output
// Module: Lean.ExtraModUses
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr import Init.Data.Range.Polymorphic.Stream
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqIndirectModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqIndirectModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqIndirectModUse___closed__0 = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqIndirectModUse = (const lean_object*)&l_Lean_instBEqIndirectModUse___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "indirectModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 173, 36, 115, 222, 236, 117, 108)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_indirectModUseExt;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__0;
static lean_once_cell_t l_Lean_getIndirectModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIndirectModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "recording indirect mod use of `"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__1;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "` ("};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__3;
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__4 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_recordIndirectModUse___redArg___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l_Lean_recordIndirectModUse___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqExtraModUse___closed__0 = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqExtraModUse = (const lean_object*)&l_Lean_instBEqExtraModUse___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableExtraModUse___closed__0 = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableExtraModUse = (const lean_object*)&l_Lean_instHashableExtraModUse___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isExported"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_instReprExtraModUse_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_instReprExtraModUse_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprExtraModUse_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_instReprExtraModUse_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprExtraModUse_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprExtraModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprExtraModUse_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprExtraModUse___closed__0 = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprExtraModUse = (const lean_object*)&l_Lean_instReprExtraModUse___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object*);
static const lean_array_object l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ExtraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 69, 125, 143, 117, 200, 37, 103)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(163, 125, 98, 145, 27, 242, 139, 173)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 80, 45, 80, 85, 236, 79, 117)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l_Lean_recordIndirectModUse___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 241, 212, 4, 163, 62, 5, 148)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__14_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__12_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__13_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__15_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
static lean_once_cell_t l_Lean_getExtraModUses___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__0;
static lean_once_cell_t l_Lean_getExtraModUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getExtraModUses___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object**);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___redArg___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___redArg___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___redArg___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isExtraRevModUseExt"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 81, 220, 33, 30, 172, 4, 212)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
static const lean_ctor_object l_Lean_isExtraRevModUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isExtraRevModUse___closed__0 = (const lean_object*)&l_Lean_isExtraRevModUse___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "recording extra reverse use of current module"};
static const lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__0_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 211, 254, 26, 237, 216, 211, 30)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__1_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__2_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 203, 147, 114, 124, 159, 234, 194)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 198, 100, 78, 72, 145, 180, 196)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__4_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 81, 65, 191, 6, 222, 76)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqIndirectModUse_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_kind_3_; lean_object* v_declName_4_; lean_object* v_kind_5_; lean_object* v_declName_6_; uint8_t v___x_7_; 
v_kind_3_ = lean_ctor_get(v_x_1_, 0);
v_declName_4_ = lean_ctor_get(v_x_1_, 1);
v_kind_5_ = lean_ctor_get(v_x_2_, 0);
v_declName_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_string_dec_eq(v_kind_3_, v_kind_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_name_eq(v_declName_4_, v_declName_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIndirectModUse_beq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_instBEqIndirectModUse_beq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_array_mk(v_es_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_s_17_, lean_object* v_x_18_){
_start:
{
lean_inc_ref(v_s_17_);
return v_s_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_s_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_s_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_s_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_52_; 
v_key_24_ = lean_ctor_get(v_x_23_, 0);
v_value_25_ = lean_ctor_get(v_x_23_, 1);
v_tail_26_ = lean_ctor_get(v_x_23_, 2);
v_isSharedCheck_52_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_52_ == 0)
{
v___x_28_ = v_x_23_;
v_isShared_29_ = v_isSharedCheck_52_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_value_25_);
lean_inc(v_key_24_);
lean_dec(v_x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_52_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; uint64_t v___y_32_; 
v___x_30_ = lean_array_get_size(v_x_22_);
if (lean_obj_tag(v_key_24_) == 0)
{
uint64_t v___x_50_; 
v___x_50_ = 1723ULL;
v___y_32_ = v___x_50_;
goto v___jp_31_;
}
else
{
uint64_t v_hash_51_; 
v_hash_51_ = lean_ctor_get_uint64(v_key_24_, sizeof(void*)*2);
v___y_32_ = v_hash_51_;
goto v___jp_31_;
}
v___jp_31_:
{
uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v_fold_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_33_ = 32ULL;
v___x_34_ = lean_uint64_shift_right(v___y_32_, v___x_33_);
v_fold_35_ = lean_uint64_xor(v___y_32_, v___x_34_);
v___x_36_ = 16ULL;
v___x_37_ = lean_uint64_shift_right(v_fold_35_, v___x_36_);
v___x_38_ = lean_uint64_xor(v_fold_35_, v___x_37_);
v___x_39_ = lean_uint64_to_usize(v___x_38_);
v___x_40_ = lean_usize_of_nat(v___x_30_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_sub(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_land(v___x_39_, v___x_42_);
v___x_44_ = lean_array_uget_borrowed(v_x_22_, v___x_43_);
lean_inc(v___x_44_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_44_);
v___x_46_ = v___x_28_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_24_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_25_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_array_uset(v_x_22_, v___x_43_, v___x_46_);
v_x_22_ = v___x_47_;
v_x_23_ = v_tail_26_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_53_, lean_object* v_source_54_, lean_object* v_target_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_array_get_size(v_source_54_);
v___x_57_ = lean_nat_dec_lt(v_i_53_, v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v_source_54_);
lean_dec(v_i_53_);
return v_target_55_;
}
else
{
lean_object* v_es_58_; lean_object* v___x_59_; lean_object* v_source_60_; lean_object* v_target_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_es_58_ = lean_array_fget(v_source_54_, v_i_53_);
v___x_59_ = lean_box(0);
v_source_60_ = lean_array_fset(v_source_54_, v_i_53_, v___x_59_);
v_target_61_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_target_55_, v_es_58_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_i_53_, v___x_62_);
lean_dec(v_i_53_);
v_i_53_ = v___x_63_;
v_source_54_ = v_source_60_;
v_target_55_ = v_target_61_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_nbuckets_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_66_ = lean_array_get_size(v_data_65_);
v___x_67_ = lean_unsigned_to_nat(2u);
v_nbuckets_68_ = lean_nat_mul(v___x_66_, v___x_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_box(0);
v___x_71_ = lean_mk_array(v_nbuckets_68_, v___x_70_);
v___x_72_ = lean_array_propagate_mark(v_data_65_, v___x_71_);
v___x_73_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_69_, v_data_65_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(lean_object* v_val_76_, lean_object* v_x_77_){
_start:
{
lean_object* v___y_79_; 
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_79_ = v___x_82_;
goto v___jp_78_;
}
else
{
lean_object* v_val_83_; 
v_val_83_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v_x_77_, 1);
v___y_79_ = v_val_83_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_array_push(v___y_79_, v_val_76_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_val_84_, lean_object* v_a_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_val_89_; lean_object* v___x_90_; 
v___x_87_ = lean_box(0);
v___x_88_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_84_, v___x_87_);
v_val_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v_a_85_);
lean_ctor_set(v___x_90_, 1, v_val_89_);
lean_ctor_set(v___x_90_, 2, v_x_86_);
return v___x_90_;
}
else
{
lean_object* v_key_91_; lean_object* v_value_92_; lean_object* v_tail_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_108_; 
v_key_91_ = lean_ctor_get(v_x_86_, 0);
v_value_92_ = lean_ctor_get(v_x_86_, 1);
v_tail_93_ = lean_ctor_get(v_x_86_, 2);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_108_ == 0)
{
v___x_95_ = v_x_86_;
v_isShared_96_ = v_isSharedCheck_108_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_tail_93_);
lean_inc(v_value_92_);
lean_inc(v_key_91_);
lean_dec(v_x_86_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_108_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v___x_97_; 
v___x_97_ = lean_name_eq(v_key_91_, v_a_85_);
if (v___x_97_ == 0)
{
lean_object* v_tail_98_; lean_object* v___x_100_; 
v_tail_98_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_84_, v_a_85_, v_tail_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 2, v_tail_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_tail_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_val_104_; lean_object* v___x_106_; 
lean_dec(v_key_91_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_value_92_);
v___x_103_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0(v_val_84_, v___x_102_);
v_val_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_104_);
lean_dec(v___x_103_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_val_104_);
lean_ctor_set(v___x_95_, 0, v_a_85_);
v___x_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_85_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_val_104_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_tail_93_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
else
{
lean_object* v_key_112_; lean_object* v_tail_113_; uint8_t v___x_114_; 
v_key_112_ = lean_ctor_get(v_x_110_, 0);
v_tail_113_ = lean_ctor_get(v_x_110_, 2);
v___x_114_ = lean_name_eq(v_key_112_, v_a_109_);
if (v___x_114_ == 0)
{
v_x_110_ = v_tail_113_;
goto _start;
}
else
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_a_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(lean_object* v_val_120_, lean_object* v_m_121_, lean_object* v_a_122_){
_start:
{
size_t v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v_size_130_; lean_object* v_buckets_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_178_; 
v_size_130_ = lean_ctor_get(v_m_121_, 0);
v_buckets_131_ = lean_ctor_get(v_m_121_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_m_121_);
if (v_isSharedCheck_178_ == 0)
{
v___x_133_ = v_m_121_;
v_isShared_134_ = v_isSharedCheck_178_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_buckets_131_);
lean_inc(v_size_130_);
lean_dec(v_m_121_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_178_;
goto v_resetjp_132_;
}
v___jp_123_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_array_uset(v___y_125_, v___y_124_, v___y_126_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
return v___x_129_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; uint64_t v___y_137_; 
v___x_135_ = lean_array_get_size(v_buckets_131_);
if (lean_obj_tag(v_a_122_) == 0)
{
uint64_t v___x_176_; 
v___x_176_ = 1723ULL;
v___y_137_ = v___x_176_;
goto v___jp_136_;
}
else
{
uint64_t v_hash_177_; 
v_hash_177_ = lean_ctor_get_uint64(v_a_122_, sizeof(void*)*2);
v___y_137_ = v_hash_177_;
goto v___jp_136_;
}
v___jp_136_:
{
uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_bkt_149_; uint8_t v___x_150_; 
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___y_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___y_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_135_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v_bkt_149_ = lean_array_uget_borrowed(v_buckets_131_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_122_, v_bkt_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_size_x27_154_; lean_object* v___x_155_; lean_object* v_buckets_x27_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_151_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___x_152_ = lean_array_push(v___x_151_, v_val_120_);
v___x_153_ = lean_unsigned_to_nat(1u);
v_size_x27_154_ = lean_nat_add(v_size_130_, v___x_153_);
lean_dec(v_size_130_);
lean_inc(v_bkt_149_);
v___x_155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_155_, 0, v_a_122_);
lean_ctor_set(v___x_155_, 1, v___x_152_);
lean_ctor_set(v___x_155_, 2, v_bkt_149_);
v_buckets_x27_156_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(4u);
v___x_158_ = lean_nat_mul(v_size_x27_154_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(3u);
v___x_160_ = lean_nat_div(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_array_get_size(v_buckets_x27_156_);
v___x_162_ = lean_nat_dec_le(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
if (v___x_162_ == 0)
{
lean_object* v_val_163_; lean_object* v___x_165_; 
v_val_163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_156_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_val_163_);
lean_ctor_set(v___x_133_, 0, v_size_x27_154_);
v___x_165_ = v___x_133_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_val_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
else
{
lean_object* v___x_168_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_buckets_x27_156_);
lean_ctor_set(v___x_133_, 0, v_size_x27_154_);
v___x_168_ = v___x_133_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_x27_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_buckets_x27_156_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v___x_170_; lean_object* v_buckets_x27_171_; lean_object* v_bkt_x27_172_; uint8_t v___x_173_; 
lean_inc(v_bkt_149_);
lean_del_object(v___x_133_);
v___x_170_ = lean_box(0);
v_buckets_x27_171_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_170_);
lean_inc(v_a_122_);
v_bkt_x27_172_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2(v_val_120_, v_a_122_, v_bkt_149_);
v___x_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_122_, v_bkt_x27_172_);
lean_dec(v_a_122_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v_size_130_, v___x_174_);
lean_dec(v_size_130_);
v___y_124_ = v___x_148_;
v___y_125_ = v_buckets_x27_171_;
v___y_126_ = v_bkt_x27_172_;
v___y_127_ = v___x_175_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_148_;
v___y_125_ = v_buckets_x27_171_;
v___y_126_ = v_bkt_x27_172_;
v___y_127_ = v_size_130_;
goto v___jp_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(lean_object* v_val_179_, lean_object* v_as_180_, size_t v_sz_181_, size_t v_i_182_, lean_object* v_b_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = lean_usize_dec_lt(v_i_182_, v_sz_181_);
if (v___x_184_ == 0)
{
lean_dec(v_val_179_);
return v_b_183_;
}
else
{
lean_object* v_a_185_; lean_object* v_declName_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; 
v_a_185_ = lean_array_uget_borrowed(v_as_180_, v_i_182_);
v_declName_186_ = lean_ctor_get(v_a_185_, 1);
lean_inc(v_declName_186_);
lean_inc(v_val_179_);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0(v_val_179_, v_b_183_, v_declName_186_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_182_, v___x_188_);
v_i_182_ = v___x_189_;
v_b_183_ = v___x_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1___boxed(lean_object* v_val_191_, lean_object* v_as_192_, lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_b_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_191_, v_as_192_, v_sz_boxed_196_, v_i_boxed_197_, v_b_195_);
lean_dec_ref(v_as_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(lean_object* v_as_199_, size_t v_sz_200_, size_t v_i_201_, lean_object* v_b_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_203_ == 0)
{
return v_b_202_;
}
else
{
lean_object* v_snd_204_; 
v_snd_204_ = lean_ctor_get(v_b_202_, 1);
lean_inc(v_snd_204_);
if (lean_obj_tag(v_snd_204_) == 0)
{
lean_object* v_fst_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_fst_205_ = lean_ctor_get(v_b_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_b_202_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_b_202_, 1);
lean_dec(v_unused_213_);
v___x_207_ = v_b_202_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_fst_205_);
lean_dec(v_b_202_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_205_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_snd_204_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_fst_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_238_; 
v_fst_214_ = lean_ctor_get(v_b_202_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_b_202_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_b_202_, 1);
lean_dec(v_unused_239_);
v___x_216_ = v_b_202_;
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_fst_214_);
lean_dec(v_b_202_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_237_; 
v_val_218_ = lean_ctor_get(v_snd_204_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_snd_204_);
if (v_isSharedCheck_237_ == 0)
{
v___x_220_ = v_snd_204_;
v_isShared_221_ = v_isSharedCheck_237_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v_snd_204_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_237_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v_a_222_ = lean_array_uget_borrowed(v_as_199_, v_i_201_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_val_218_, v___x_223_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_224_);
v___x_226_ = v___x_220_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_236_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
size_t v_sz_227_; size_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v_sz_227_ = lean_array_size(v_a_222_);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__1(v_val_218_, v_a_222_, v_sz_227_, v___x_228_, v_fst_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_226_);
lean_ctor_set(v___x_216_, 0, v___x_229_);
v___x_231_ = v___x_216_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_226_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
size_t v___x_232_; size_t v___x_233_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_add(v_i_201_, v___x_232_);
v_i_201_ = v___x_233_;
v_b_202_ = v___x_231_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_as_240_, v_sz_boxed_244_, v_i_boxed_245_, v_b_243_);
lean_dec_ref(v_as_240_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_unsigned_to_nat(16u);
v___x_249_ = lean_mk_array(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_s_252_; 
v___x_250_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_251_ = lean_unsigned_to_nat(0u);
v_s_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_252_, 0, v___x_251_);
lean_ctor_set(v_s_252_, 1, v___x_250_);
return v_s_252_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_255_; lean_object* v_s_256_; lean_object* v___x_257_; 
v___x_255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v_s_256_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_s_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(lean_object* v_es_258_){
_start:
{
lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v___x_262_; lean_object* v_fst_263_; 
v___x_259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_);
v_sz_260_ = lean_array_size(v_es_258_);
v___x_261_ = ((size_t)0ULL);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__2(v_es_258_, v_sz_260_, v___x_261_, v___x_259_);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
lean_dec_ref(v___x_262_);
return v_fst_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_es_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(v_es_264_);
lean_dec_ref(v_es_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_));
v___x_283_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2____boxed(lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_286_, lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_287_, v_x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_290_, lean_object* v_a_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_290_, v_a_291_, v_x_292_);
lean_dec(v_x_292_);
lean_dec(v_a_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_295_, lean_object* v_data_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_298_, lean_object* v_i_299_, lean_object* v_source_300_, lean_object* v_target_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_299_, v_source_300_, v_target_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__5___redArg(v_x_304_, v_x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__0(void){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_HashMap_instInhabited___redArg();
return v___x_307_;
}
}
static lean_object* _init_l_Lean_getIndirectModUses___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses(lean_object* v_env_311_, lean_object* v_modIdx_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__1, &l_Lean_getIndirectModUses___closed__1_once, _init_l_Lean_getIndirectModUses___closed__1);
v___x_314_ = l_Lean_indirectModUseExt;
v___x_315_ = 0;
v___x_316_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_313_, v___x_314_, v_env_311_, v_modIdx_312_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getIndirectModUses___boxed(lean_object* v_env_317_, lean_object* v_modIdx_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_getIndirectModUses(v_env_317_, v_modIdx_318_);
lean_dec(v_modIdx_318_);
lean_dec_ref(v_env_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__0(lean_object* v___x_320_, lean_object* v___x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_toEnvExtension_323_; lean_object* v_asyncMode_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_toEnvExtension_323_ = lean_ctor_get(v___x_320_, 0);
v_asyncMode_324_ = lean_ctor_get(v_toEnvExtension_323_, 2);
lean_inc(v_asyncMode_324_);
v___x_325_ = lean_box(0);
v___x_326_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_320_, v_x_322_, v___x_321_, v_asyncMode_324_, v___x_325_);
lean_dec(v_asyncMode_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__1(lean_object* v_modifyEnv_327_, lean_object* v___f_328_, lean_object* v_____r_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_apply_1(v_modifyEnv_327_, v___f_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2(lean_object* v_toPure_334_, lean_object* v_cls_335_, lean_object* v_____do__lift_336_, lean_object* v_____do__lift_337_){
_start:
{
uint8_t v_hasTrace_338_; 
v_hasTrace_338_ = lean_ctor_get_uint8(v_____do__lift_337_, sizeof(void*)*1);
if (v_hasTrace_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_cls_335_);
v___x_339_ = lean_box(v_hasTrace_338_);
v___x_340_ = lean_apply_2(v_toPure_334_, lean_box(0), v___x_339_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_341_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__2___closed__1));
v___x_342_ = l_Lean_Name_append(v___x_341_, v_cls_335_);
v___x_343_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_336_, v_____do__lift_337_, v___x_342_);
lean_dec(v___x_342_);
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_apply_2(v_toPure_334_, lean_box(0), v___x_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__2___boxed(lean_object* v_toPure_346_, lean_object* v_cls_347_, lean_object* v_____do__lift_348_, lean_object* v_____do__lift_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_recordIndirectModUse___redArg___lam__2(v_toPure_346_, v_cls_347_, v_____do__lift_348_, v_____do__lift_349_);
lean_dec_ref(v_____do__lift_349_);
lean_dec_ref(v_____do__lift_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__3(lean_object* v_inst_351_, lean_object* v_toPure_352_, lean_object* v_cls_353_, lean_object* v_toBind_354_, lean_object* v_____do__lift_355_){
_start:
{
lean_object* v_getOptionsUnrestricted_356_; lean_object* v___f_357_; lean_object* v___x_358_; 
v_getOptionsUnrestricted_356_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_getOptionsUnrestricted_356_);
lean_dec_ref(v_inst_351_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_357_, 0, v_toPure_352_);
lean_closure_set(v___f_357_, 1, v_cls_353_);
lean_closure_set(v___f_357_, 2, v_____do__lift_355_);
v___x_358_ = lean_apply_4(v_toBind_354_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_356_, v___f_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__0));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__3(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__2));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__5(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__4___closed__4));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4(lean_object* v_modifyEnv_368_, lean_object* v___f_369_, lean_object* v_declName_370_, lean_object* v_kind_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_cls_376_, lean_object* v_toBind_377_, lean_object* v___f_378_, uint8_t v_____do__lift_379_){
_start:
{
if (v_____do__lift_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v___f_378_);
lean_dec(v_toBind_377_);
lean_dec(v_cls_376_);
lean_dec(v_inst_375_);
lean_dec_ref(v_inst_374_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
lean_dec_ref(v_kind_371_);
lean_dec(v_declName_370_);
v___x_380_ = lean_apply_1(v_modifyEnv_368_, v___f_369_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v___f_369_);
lean_dec(v_modifyEnv_368_);
v___x_381_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__1, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__1_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__1);
v___x_382_ = l_Lean_MessageData_ofName(v_declName_370_);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__3, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__3_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__3);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_stringToMessageData(v_kind_371_);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_obj_once(&l_Lean_recordIndirectModUse___redArg___lam__4___closed__5, &l_Lean_recordIndirectModUse___redArg___lam__4___closed__5_once, _init_l_Lean_recordIndirectModUse___redArg___lam__4___closed__5);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_addTrace___redArg(v_inst_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_cls_376_, v___x_389_);
v___x_391_ = lean_apply_4(v_toBind_377_, lean_box(0), lean_box(0), v___x_390_, v___f_378_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__4___boxed(lean_object* v_modifyEnv_392_, lean_object* v___f_393_, lean_object* v_declName_394_, lean_object* v_kind_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_cls_400_, lean_object* v_toBind_401_, lean_object* v___f_402_, lean_object* v_____do__lift_403_){
_start:
{
uint8_t v_____do__lift_445__boxed_404_; lean_object* v_res_405_; 
v_____do__lift_445__boxed_404_ = lean_unbox(v_____do__lift_403_);
v_res_405_ = l_Lean_recordIndirectModUse___redArg___lam__4(v_modifyEnv_392_, v___f_393_, v_declName_394_, v_kind_395_, v_inst_396_, v_inst_397_, v_inst_398_, v_inst_399_, v_cls_400_, v_toBind_401_, v___f_402_, v_____do__lift_445__boxed_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg___lam__5(lean_object* v___x_409_, lean_object* v_kind_410_, lean_object* v_declName_411_, lean_object* v___x_412_, lean_object* v_inst_413_, lean_object* v_modifyEnv_414_, lean_object* v_inst_415_, lean_object* v_toPure_416_, lean_object* v_toBind_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_____do__lift_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_422_ = l_Lean_indirectModUseExt;
v___x_423_ = lean_box(2);
v___x_424_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_409_, v___x_422_, v_____do__lift_421_, v___x_423_);
lean_inc(v_declName_411_);
lean_inc_ref(v_kind_410_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_kind_410_);
lean_ctor_set(v___x_425_, 1, v_declName_411_);
lean_inc_ref(v___x_425_);
v___x_426_ = l_List_elem___redArg(v___x_412_, v___x_425_, v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v_getInheritedTraceOptions_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v_cls_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_getInheritedTraceOptions_427_ = lean_ctor_get(v_inst_413_, 2);
lean_inc(v_getInheritedTraceOptions_427_);
v___f_428_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__0), 3, 2);
lean_closure_set(v___f_428_, 0, v___x_422_);
lean_closure_set(v___f_428_, 1, v___x_425_);
lean_inc_ref(v___f_428_);
lean_inc(v_modifyEnv_414_);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_429_, 0, v_modifyEnv_414_);
lean_closure_set(v___f_429_, 1, v___f_428_);
v_cls_430_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_417_, 3);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_431_, 0, v_inst_415_);
lean_closure_set(v___f_431_, 1, v_toPure_416_);
lean_closure_set(v___f_431_, 2, v_cls_430_);
lean_closure_set(v___f_431_, 3, v_toBind_417_);
v___f_432_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_432_, 0, v_modifyEnv_414_);
lean_closure_set(v___f_432_, 1, v___f_428_);
lean_closure_set(v___f_432_, 2, v_declName_411_);
lean_closure_set(v___f_432_, 3, v_kind_410_);
lean_closure_set(v___f_432_, 4, v_inst_418_);
lean_closure_set(v___f_432_, 5, v_inst_413_);
lean_closure_set(v___f_432_, 6, v_inst_419_);
lean_closure_set(v___f_432_, 7, v_inst_420_);
lean_closure_set(v___f_432_, 8, v_cls_430_);
lean_closure_set(v___f_432_, 9, v_toBind_417_);
lean_closure_set(v___f_432_, 10, v___f_429_);
v___x_433_ = lean_apply_4(v_toBind_417_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_427_, v___f_431_);
v___x_434_ = lean_apply_4(v_toBind_417_, lean_box(0), lean_box(0), v___x_433_, v___f_432_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref_known(v___x_425_, 2);
lean_dec(v_inst_420_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
lean_dec(v_toBind_417_);
lean_dec_ref(v_inst_415_);
lean_dec(v_modifyEnv_414_);
lean_dec_ref(v_inst_413_);
lean_dec(v_declName_411_);
lean_dec_ref(v_kind_410_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_apply_2(v_toPure_416_, lean_box(0), v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse___redArg(lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_kind_443_, lean_object* v_declName_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_getEnv_447_; lean_object* v_modifyEnv_448_; lean_object* v_toPure_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_437_, 0);
v_toBind_446_ = lean_ctor_get(v_inst_437_, 1);
lean_inc_n(v_toBind_446_, 2);
v_getEnv_447_ = lean_ctor_get(v_inst_438_, 0);
lean_inc(v_getEnv_447_);
v_modifyEnv_448_ = lean_ctor_get(v_inst_438_, 1);
lean_inc(v_modifyEnv_448_);
lean_dec_ref(v_inst_438_);
v_toPure_449_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_449_);
v___x_450_ = ((lean_object*)(l_Lean_instBEqIndirectModUse___closed__0));
v___x_451_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___f_452_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__5), 13, 12);
lean_closure_set(v___f_452_, 0, v___x_451_);
lean_closure_set(v___f_452_, 1, v_kind_443_);
lean_closure_set(v___f_452_, 2, v_declName_444_);
lean_closure_set(v___f_452_, 3, v___x_450_);
lean_closure_set(v___f_452_, 4, v_inst_439_);
lean_closure_set(v___f_452_, 5, v_modifyEnv_448_);
lean_closure_set(v___f_452_, 6, v_inst_440_);
lean_closure_set(v___f_452_, 7, v_toPure_449_);
lean_closure_set(v___f_452_, 8, v_toBind_446_);
lean_closure_set(v___f_452_, 9, v_inst_437_);
lean_closure_set(v___f_452_, 10, v_inst_441_);
lean_closure_set(v___f_452_, 11, v_inst_442_);
v___x_453_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v_getEnv_447_, v___f_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordIndirectModUse(lean_object* v_m_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_kind_461_, lean_object* v_declName_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_recordIndirectModUse___redArg(v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_kind_461_, v_declName_462_);
return v___x_463_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqExtraModUse_beq(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_module_466_; uint8_t v_isExported_467_; uint8_t v_isMeta_468_; lean_object* v_module_469_; uint8_t v_isExported_470_; uint8_t v_isMeta_471_; uint8_t v___y_473_; uint8_t v___x_474_; 
v_module_466_ = lean_ctor_get(v_x_464_, 0);
v_isExported_467_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*1);
v_isMeta_468_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*1 + 1);
v_module_469_ = lean_ctor_get(v_x_465_, 0);
v_isExported_470_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*1);
v_isMeta_471_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*1 + 1);
v___x_474_ = lean_name_eq(v_module_466_, v_module_469_);
if (v___x_474_ == 0)
{
return v___x_474_;
}
else
{
if (v_isExported_470_ == 0)
{
if (v_isExported_467_ == 0)
{
v___y_473_ = v___x_474_;
goto v___jp_472_;
}
else
{
return v_isExported_470_;
}
}
else
{
v___y_473_ = v_isExported_467_;
goto v___jp_472_;
}
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
return v___y_473_;
}
else
{
if (v_isMeta_471_ == 0)
{
if (v_isMeta_468_ == 0)
{
return v___y_473_;
}
else
{
return v_isMeta_471_;
}
}
else
{
return v_isMeta_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_instBEqExtraModUse_beq(v_x_475_, v_x_476_);
lean_dec_ref(v_x_476_);
lean_dec_ref(v_x_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableExtraModUse_hash(lean_object* v_x_481_){
_start:
{
lean_object* v_module_482_; uint8_t v_isExported_483_; uint8_t v_isMeta_484_; uint64_t v___y_486_; uint64_t v___y_487_; uint64_t v___x_493_; uint64_t v___y_495_; 
v_module_482_ = lean_ctor_get(v_x_481_, 0);
v_isExported_483_ = lean_ctor_get_uint8(v_x_481_, sizeof(void*)*1);
v_isMeta_484_ = lean_ctor_get_uint8(v_x_481_, sizeof(void*)*1 + 1);
v___x_493_ = 0ULL;
if (lean_obj_tag(v_module_482_) == 0)
{
uint64_t v___x_499_; 
v___x_499_ = 1723ULL;
v___y_495_ = v___x_499_;
goto v___jp_494_;
}
else
{
uint64_t v_hash_500_; 
v_hash_500_ = lean_ctor_get_uint64(v_module_482_, sizeof(void*)*2);
v___y_495_ = v_hash_500_;
goto v___jp_494_;
}
v___jp_485_:
{
uint64_t v___x_488_; 
v___x_488_ = lean_uint64_mix_hash(v___y_486_, v___y_487_);
if (v_isMeta_484_ == 0)
{
uint64_t v___x_489_; uint64_t v___x_490_; 
v___x_489_ = 13ULL;
v___x_490_ = lean_uint64_mix_hash(v___x_488_, v___x_489_);
return v___x_490_;
}
else
{
uint64_t v___x_491_; uint64_t v___x_492_; 
v___x_491_ = 11ULL;
v___x_492_ = lean_uint64_mix_hash(v___x_488_, v___x_491_);
return v___x_492_;
}
}
v___jp_494_:
{
uint64_t v___x_496_; 
v___x_496_ = lean_uint64_mix_hash(v___x_493_, v___y_495_);
if (v_isExported_483_ == 0)
{
uint64_t v___x_497_; 
v___x_497_ = 13ULL;
v___y_486_ = v___x_496_;
v___y_487_ = v___x_497_;
goto v___jp_485_;
}
else
{
uint64_t v___x_498_; 
v___x_498_ = 11ULL;
v___y_486_ = v___x_496_;
v___y_487_ = v___x_498_;
goto v___jp_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object* v_x_501_){
_start:
{
uint64_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Lean_instHashableExtraModUse_hash(v_x_501_);
lean_dec_ref(v_x_501_);
v_r_503_ = lean_box_uint64(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprExtraModUse_repr_spec__0(lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_nat_to_int(v_a_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(10u);
v___x_522_ = lean_nat_to_int(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(14u);
v___x_530_ = lean_nat_to_int(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__0));
v___x_536_ = lean_string_length(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__16, &l_Lean_instReprExtraModUse_repr___redArg___closed__16_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__16);
v___x_538_ = lean_nat_to_int(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___redArg(lean_object* v_x_543_){
_start:
{
lean_object* v_module_544_; uint8_t v_isExported_545_; uint8_t v_isMeta_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_module_544_ = lean_ctor_get(v_x_543_, 0);
lean_inc(v_module_544_);
v_isExported_545_ = lean_ctor_get_uint8(v_x_543_, sizeof(void*)*1);
v_isMeta_546_ = lean_ctor_get_uint8(v_x_543_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_543_);
v___x_547_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__5));
v___x_548_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__6));
v___x_549_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__7, &l_Lean_instReprExtraModUse_repr___redArg___closed__7_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__7);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = l_Lean_Name_reprPrec(v_module_544_, v___x_550_);
v___x_552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = 0;
v___x_554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_553_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_548_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__9));
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_box(1);
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__11));
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_547_);
v___x_563_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__12, &l_Lean_instReprExtraModUse_repr___redArg___closed__12_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__12);
v___x_564_ = l_Bool_repr___redArg(v_isExported_545_);
v___x_565_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_553_);
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_562_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_556_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_558_);
v___x_570_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__14));
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_547_);
v___x_573_ = l_Bool_repr___redArg(v_isMeta_546_);
v___x_574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_549_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*1, v___x_553_);
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_572_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_instReprExtraModUse_repr___redArg___closed__17, &l_Lean_instReprExtraModUse_repr___redArg___closed__17_once, _init_l_Lean_instReprExtraModUse_repr___redArg___closed__17);
v___x_578_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__18));
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_576_);
v___x_580_ = ((lean_object*)(l_Lean_instReprExtraModUse_repr___redArg___closed__19));
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_577_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_553_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr(lean_object* v_x_584_, lean_object* v_prec_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_instReprExtraModUse_repr___redArg(v_x_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExtraModUse_repr___boxed(lean_object* v_x_587_, lean_object* v_prec_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_instReprExtraModUse_repr(v_x_587_, v_prec_588_);
lean_dec(v_prec_588_);
return v_res_589_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_592_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg(){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___closed__1);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___dummy_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
return v_res_598_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___redArg();
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_entries_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_608_ = lean_array_mk(v_entries_606_);
v___x_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_entries_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_610_, v_x_611_, v_entries_612_);
lean_dec_ref(v_x_611_);
lean_dec_ref(v_x_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_es_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_mk(v_es_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__1___closed__0);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(v_x_618_);
lean_dec_ref(v_x_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_ks_624_; lean_object* v_vs_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_649_; 
v_ks_624_ = lean_ctor_get(v_x_620_, 0);
v_vs_625_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_649_ == 0)
{
v___x_627_ = v_x_620_;
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_vs_625_);
lean_inc(v_ks_624_);
lean_dec(v_x_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_ks_624_);
v___x_630_ = lean_nat_dec_lt(v_x_621_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_dec(v_x_621_);
v___x_631_ = lean_array_push(v_ks_624_, v_x_622_);
v___x_632_ = lean_array_push(v_vs_625_, v_x_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_632_);
lean_ctor_set(v___x_627_, 0, v___x_631_);
v___x_634_ = v___x_627_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
lean_object* v_k_x27_636_; uint8_t v___x_637_; 
v_k_x27_636_ = lean_array_fget_borrowed(v_ks_624_, v_x_621_);
v___x_637_ = l_Lean_instBEqExtraModUse_beq(v_x_622_, v_k_x27_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; 
if (v_isShared_628_ == 0)
{
v___x_639_ = v___x_627_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_ks_624_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_vs_625_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_x_621_, v___x_640_);
lean_dec(v_x_621_);
v_x_620_ = v___x_639_;
v_x_621_ = v___x_641_;
goto _start;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_array_fset(v_ks_624_, v_x_621_, v_x_622_);
v___x_645_ = lean_array_fset(v_vs_625_, v_x_621_, v_x_623_);
lean_dec(v_x_621_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_645_);
lean_ctor_set(v___x_627_, 0, v___x_644_);
v___x_647_ = v___x_627_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(lean_object* v_n_650_, lean_object* v_k_651_, lean_object* v_v_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_n_650_, v___x_653_, v_k_651_, v_v_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_x_656_, size_t v_x_657_, size_t v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_es_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_j_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_es_661_ = lean_ctor_get(v_x_656_, 0);
v___x_662_ = ((size_t)31ULL);
v___x_663_ = lean_usize_land(v_x_657_, v___x_662_);
v_j_664_ = lean_usize_to_nat(v___x_663_);
v___x_665_ = lean_array_get_size(v_es_661_);
v___x_666_ = lean_nat_dec_lt(v_j_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_j_664_);
lean_dec(v_x_660_);
lean_dec_ref(v_x_659_);
return v_x_656_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_705_; 
lean_inc_ref(v_es_661_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_x_656_, 0);
lean_dec(v_unused_706_);
v___x_668_ = v_x_656_;
v_isShared_669_ = v_isSharedCheck_705_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_x_656_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_705_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_xs_x27_672_; lean_object* v___y_674_; 
v_v_670_ = lean_array_fget(v_es_661_, v_j_664_);
v___x_671_ = lean_box(0);
v_xs_x27_672_ = lean_array_fset(v_es_661_, v_j_664_, v___x_671_);
switch(lean_obj_tag(v_v_670_))
{
case 0:
{
lean_object* v_key_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_690_; 
v_key_679_ = lean_ctor_get(v_v_670_, 0);
v_val_680_ = lean_ctor_get(v_v_670_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_682_ = v_v_670_;
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_inc(v_key_679_);
lean_dec(v_v_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_instBEqExtraModUse_beq(v_x_659_, v_key_679_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_682_);
v___x_685_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_679_, v_val_680_, v_x_659_, v_x_660_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___y_674_ = v___x_686_;
goto v___jp_673_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v_val_680_);
lean_dec(v_key_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_x_660_);
lean_ctor_set(v___x_682_, 0, v_x_659_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_x_659_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_x_660_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_674_ = v___x_688_;
goto v___jp_673_;
}
}
}
}
case 1:
{
lean_object* v_node_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_703_; 
v_node_691_ = lean_ctor_get(v_v_670_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_703_ == 0)
{
v___x_693_ = v_v_670_;
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_node_691_);
lean_dec(v_v_670_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_695_ = ((size_t)5ULL);
v___x_696_ = lean_usize_shift_right(v_x_657_, v___x_695_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_x_658_, v___x_697_);
v___x_699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_node_691_, v___x_696_, v___x_698_, v_x_659_, v_x_660_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_699_);
v___x_701_ = v___x_693_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v___y_674_ = v___x_701_;
goto v___jp_673_;
}
}
}
default: 
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_x_659_);
lean_ctor_set(v___x_704_, 1, v_x_660_);
v___y_674_ = v___x_704_;
goto v___jp_673_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_array_fset(v_xs_x27_672_, v_j_664_, v___y_674_);
lean_dec(v_j_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
else
{
lean_object* v_ks_707_; lean_object* v_vs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_726_; 
v_ks_707_ = lean_ctor_get(v_x_656_, 0);
v_vs_708_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_726_ == 0)
{
v___x_710_ = v_x_656_;
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_vs_708_);
lean_inc(v_ks_707_);
lean_dec(v_x_656_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_ks_707_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_vs_708_);
v___x_713_ = v_reuseFailAlloc_725_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v_newNode_714_; size_t v___x_715_; uint8_t v___x_716_; 
v_newNode_714_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v___x_713_, v_x_659_, v_x_660_);
v___x_715_ = ((size_t)7ULL);
v___x_716_ = lean_usize_dec_le(v___x_715_, v_x_658_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_714_);
v___x_718_ = lean_unsigned_to_nat(4u);
v___x_719_ = lean_nat_dec_lt(v___x_717_, v___x_718_);
lean_dec(v___x_717_);
if (v___x_719_ == 0)
{
lean_object* v_ks_720_; lean_object* v_vs_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_ks_720_ = lean_ctor_get(v_newNode_714_, 0);
lean_inc_ref(v_ks_720_);
v_vs_721_ = lean_ctor_get(v_newNode_714_, 1);
lean_inc_ref(v_vs_721_);
lean_dec_ref(v_newNode_714_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___closed__0);
v___x_724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_x_658_, v_ks_720_, v_vs_721_, v___x_722_, v___x_723_);
lean_dec_ref(v_vs_721_);
lean_dec_ref(v_ks_720_);
return v___x_724_;
}
else
{
return v_newNode_714_;
}
}
else
{
return v_newNode_714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(size_t v_depth_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v_keys_728_);
v___x_733_ = lean_nat_dec_lt(v_i_730_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v_i_730_);
return v_entries_731_;
}
else
{
lean_object* v_k_734_; lean_object* v_v_735_; uint64_t v___x_736_; size_t v_h_737_; size_t v___x_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v_h_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_k_734_ = lean_array_fget_borrowed(v_keys_728_, v_i_730_);
v_v_735_ = lean_array_fget_borrowed(v_vals_729_, v_i_730_);
v___x_736_ = l_Lean_instHashableExtraModUse_hash(v_k_734_);
v_h_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = ((size_t)5ULL);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_sub(v_depth_727_, v___x_740_);
v___x_742_ = lean_usize_mul(v___x_738_, v___x_741_);
v_h_743_ = lean_usize_shift_right(v_h_737_, v___x_742_);
v___x_744_ = lean_nat_add(v_i_730_, v___x_739_);
lean_dec(v_i_730_);
lean_inc(v_v_735_);
lean_inc(v_k_734_);
v___x_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_entries_731_, v_h_743_, v_depth_727_, v_k_734_, v_v_735_);
v_i_730_ = v___x_744_;
v_entries_731_ = v___x_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_i_750_, lean_object* v_entries_751_){
_start:
{
size_t v_depth_boxed_752_; lean_object* v_res_753_; 
v_depth_boxed_752_ = lean_unbox_usize(v_depth_747_);
lean_dec(v_depth_747_);
v_res_753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_boxed_752_, v_keys_748_, v_vals_749_, v_i_750_, v_entries_751_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
size_t v_x_581__boxed_759_; size_t v_x_582__boxed_760_; lean_object* v_res_761_; 
v_x_581__boxed_759_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_x_582__boxed_760_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_res_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_754_, v_x_581__boxed_759_, v_x_582__boxed_760_, v_x_757_, v_x_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint64_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_765_ = l_Lean_instHashableExtraModUse_hash(v_x_763_);
v___x_766_ = lean_uint64_to_usize(v___x_765_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_762_, v___x_766_, v___x_767_, v_x_763_, v_x_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__3_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(lean_object* v_m_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_m_769_, v_k_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_keys_773_, lean_object* v_i_774_, lean_object* v_k_775_){
_start:
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = lean_array_get_size(v_keys_773_);
v___x_777_ = lean_nat_dec_lt(v_i_774_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v_i_774_);
return v___x_777_;
}
else
{
lean_object* v_k_x27_778_; uint8_t v___x_779_; 
v_k_x27_778_ = lean_array_fget_borrowed(v_keys_773_, v_i_774_);
v___x_779_ = l_Lean_instBEqExtraModUse_beq(v_k_775_, v_k_x27_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_i_774_, v___x_780_);
lean_dec(v_i_774_);
v_i_774_ = v___x_781_;
goto _start;
}
else
{
lean_dec(v_i_774_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_783_, lean_object* v_i_784_, lean_object* v_k_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_783_, v_i_784_, v_k_785_);
lean_dec_ref(v_k_785_);
lean_dec_ref(v_keys_783_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_788_, size_t v_x_789_, lean_object* v_x_790_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v_es_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v_j_795_; lean_object* v___x_796_; 
v_es_791_ = lean_ctor_get(v_x_788_, 0);
v___x_792_ = lean_box(2);
v___x_793_ = ((size_t)31ULL);
v___x_794_ = lean_usize_land(v_x_789_, v___x_793_);
v_j_795_ = lean_usize_to_nat(v___x_794_);
v___x_796_ = lean_array_get_borrowed(v___x_792_, v_es_791_, v_j_795_);
lean_dec(v_j_795_);
switch(lean_obj_tag(v___x_796_))
{
case 0:
{
lean_object* v_key_797_; uint8_t v___x_798_; 
v_key_797_ = lean_ctor_get(v___x_796_, 0);
v___x_798_ = l_Lean_instBEqExtraModUse_beq(v_x_790_, v_key_797_);
return v___x_798_;
}
case 1:
{
lean_object* v_node_799_; size_t v___x_800_; size_t v___x_801_; 
v_node_799_ = lean_ctor_get(v___x_796_, 0);
v___x_800_ = ((size_t)5ULL);
v___x_801_ = lean_usize_shift_right(v_x_789_, v___x_800_);
v_x_788_ = v_node_799_;
v_x_789_ = v___x_801_;
goto _start;
}
default: 
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
else
{
lean_object* v_ks_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_ks_804_ = lean_ctor_get(v_x_788_, 0);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_ks_804_, v___x_805_, v_x_790_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_763__boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v_x_763__boxed_810_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_res_811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_807_, v_x_763__boxed_810_, v_x_809_);
lean_dec_ref(v_x_809_);
lean_dec_ref(v_x_807_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
uint64_t v___x_815_; size_t v___x_816_; uint8_t v___x_817_; 
v___x_815_ = l_Lean_instHashableExtraModUse_hash(v_x_814_);
v___x_816_ = lean_uint64_to_usize(v___x_815_);
v___x_817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_813_, v___x_816_, v_x_814_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_818_, v_x_819_);
lean_dec_ref(v_x_819_);
lean_dec_ref(v_x_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__16_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_));
v___x_864_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2____boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
return v_res_866_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0(v_00_u03b2_871_, v_x_872_, v_x_873_);
lean_dec_ref(v_x_873_);
lean_dec_ref(v_x_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2___redArg(v_x_877_, v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, size_t v_x_883_, lean_object* v_x_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_882_, v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
size_t v_x_961__boxed_890_; uint8_t v_res_891_; lean_object* v_r_892_; 
v_x_961__boxed_890_ = lean_unbox_usize(v_x_888_);
lean_dec(v_x_888_);
v_res_891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_886_, v_x_887_, v_x_961__boxed_890_, v_x_889_);
lean_dec_ref(v_x_889_);
lean_dec_ref(v_x_887_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, size_t v_x_895_, size_t v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___redArg(v_x_894_, v_x_895_, v_x_896_, v_x_897_, v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b2_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_972__boxed_906_; size_t v_x_973__boxed_907_; lean_object* v_res_908_; 
v_x_972__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_x_973__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_900_, v_x_901_, v_x_972__boxed_906_, v_x_973__boxed_907_, v_x_904_, v_x_905_);
return v_res_908_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_909_, lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_heq_912_, lean_object* v_i_913_, lean_object* v_k_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_keys_910_, v_i_913_, v_k_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_heq_919_, lean_object* v_i_920_, lean_object* v_k_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_916_, v_keys_917_, v_vals_918_, v_heq_919_, v_i_920_, v_k_921_);
lean_dec_ref(v_k_921_);
lean_dec_ref(v_vals_918_);
lean_dec_ref(v_keys_917_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_00_u03b2_924_, lean_object* v_n_925_, lean_object* v_k_926_, lean_object* v_v_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5___redArg(v_n_925_, v_k_926_, v_v_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(lean_object* v_00_u03b2_929_, size_t v_depth_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_entries_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___redArg(v_depth_930_, v_keys_931_, v_vals_932_, v_i_934_, v_entries_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_937_, lean_object* v_depth_938_, lean_object* v_keys_939_, lean_object* v_vals_940_, lean_object* v_heq_941_, lean_object* v_i_942_, lean_object* v_entries_943_){
_start:
{
size_t v_depth_boxed_944_; lean_object* v_res_945_; 
v_depth_boxed_944_ = lean_unbox_usize(v_depth_938_);
lean_dec(v_depth_938_);
v_res_945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__6(v_00_u03b2_937_, v_depth_boxed_944_, v_keys_939_, v_vals_940_, v_heq_941_, v_i_942_, v_entries_943_);
lean_dec_ref(v_vals_940_);
lean_dec_ref(v_keys_939_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__6___redArg(v_x_947_, v_x_948_, v_x_949_, v_x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__0(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_952_;
}
}
static lean_object* _init_l_Lean_getExtraModUses___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses(lean_object* v_env_956_, lean_object* v_modIdx_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v___x_958_ = lean_obj_once(&l_Lean_getExtraModUses___closed__1, &l_Lean_getExtraModUses___closed__1_once, _init_l_Lean_getExtraModUses___closed__1);
v___x_959_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_960_ = 0;
v___x_961_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_958_, v___x_959_, v_env_956_, v_modIdx_957_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExtraModUses___boxed(lean_object* v_env_962_, lean_object* v_modIdx_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_getExtraModUses(v_env_962_, v_modIdx_963_);
lean_dec(v_modIdx_963_);
lean_dec_ref(v_env_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(lean_object* v_as_x27_965_, lean_object* v_b_966_){
_start:
{
if (lean_obj_tag(v_as_x27_965_) == 0)
{
return v_b_966_;
}
else
{
lean_object* v_head_967_; lean_object* v_tail_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_head_967_ = lean_ctor_get(v_as_x27_965_, 0);
v_tail_968_ = lean_ctor_get(v_as_x27_965_, 1);
v___x_969_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_970_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_971_ = lean_box(1);
v___x_972_ = lean_box(0);
lean_inc_ref(v_b_966_);
v___x_973_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_969_, v___x_970_, v_b_966_, v___x_971_, v___x_972_);
v___x_974_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2__spec__0___redArg(v___x_973_, v_head_967_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v_toEnvExtension_975_; lean_object* v_asyncMode_976_; lean_object* v___x_977_; 
v_toEnvExtension_975_ = lean_ctor_get(v___x_970_, 0);
v_asyncMode_976_ = lean_ctor_get(v_toEnvExtension_975_, 2);
lean_inc(v_head_967_);
v___x_977_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_970_, v_b_966_, v_head_967_, v_asyncMode_976_, v___x_972_);
v_as_x27_965_ = v_tail_968_;
v_b_966_ = v___x_977_;
goto _start;
}
else
{
v_as_x27_965_ = v_tail_968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg___boxed(lean_object* v_as_x27_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_980_, v_b_981_);
lean_dec(v_as_x27_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_copyExtraModUses(lean_object* v_src_983_, lean_object* v_dest_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_985_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_986_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_987_ = lean_box(1);
v___x_988_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_985_, v___x_986_, v_src_983_, v___x_987_);
v___x_989_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v___x_988_, v_dest_984_);
lean_dec(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(lean_object* v_as_990_, lean_object* v_as_x27_991_, lean_object* v_b_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___redArg(v_as_x27_991_, v_b_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0___boxed(lean_object* v_as_995_, lean_object* v_as_x27_996_, lean_object* v_b_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_List_forIn_x27_loop___at___00Lean_copyExtraModUses_spec__0(v_as_995_, v_as_x27_996_, v_b_997_, v_a_998_);
lean_dec(v_as_x27_996_);
lean_dec(v_as_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0(lean_object* v___x_1000_, lean_object* v_entry_1001_, lean_object* v___x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v_toEnvExtension_1004_; lean_object* v_asyncMode_1005_; lean_object* v___x_1006_; 
v_toEnvExtension_1004_ = lean_ctor_get(v___x_1000_, 0);
v_asyncMode_1005_ = lean_ctor_get(v_toEnvExtension_1004_, 2);
lean_inc(v_asyncMode_1005_);
v___x_1006_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1000_, v_x_1003_, v_entry_1001_, v_asyncMode_1005_, v___x_1002_);
lean_dec(v_asyncMode_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__0));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__2));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__4));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__6));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__8));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(lean_object* v_modifyEnv_1026_, lean_object* v___f_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_cls_1032_, lean_object* v_toBind_1033_, lean_object* v___f_1034_, lean_object* v_mod_1035_, lean_object* v_hint_1036_, uint8_t v_isMeta_1037_, uint8_t v_isExporting_1038_, uint8_t v_____do__lift_1039_){
_start:
{
lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1047_; lean_object* v___y_1048_; 
if (v_____do__lift_1039_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_hint_1036_);
lean_dec(v_mod_1035_);
lean_dec(v___f_1034_);
lean_dec(v_toBind_1033_);
lean_dec(v_cls_1032_);
lean_dec(v_inst_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
lean_dec_ref(v_inst_1028_);
v___x_1060_ = lean_apply_1(v_modifyEnv_1026_, v___f_1027_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___y_1063_; 
lean_dec_ref(v___f_1027_);
lean_dec(v_modifyEnv_1026_);
v___x_1061_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__7);
if (v_isExporting_1038_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__12));
v___y_1063_ = v___x_1070_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__13));
v___y_1063_ = v___x_1071_;
goto v___jp_1062_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc_ref(v___y_1063_);
v___x_1064_ = l_Lean_stringToMessageData(v___y_1063_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1061_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__9);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isMeta_1037_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__10));
v___y_1047_ = v___x_1067_;
v___y_1048_ = v___x_1068_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__11));
v___y_1047_ = v___x_1067_;
v___y_1048_ = v___x_1069_;
goto v___jp_1046_;
}
}
}
v___jp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___y_1041_);
lean_ctor_set(v___x_1043_, 1, v___y_1042_);
v___x_1044_ = l_Lean_addTrace___redArg(v_inst_1028_, v_inst_1029_, v_inst_1030_, v_inst_1031_, v_cls_1032_, v___x_1043_);
v___x_1045_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v___x_1044_, v___f_1034_);
return v___x_1045_;
}
v___jp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
lean_inc_ref(v___y_1048_);
v___x_1049_ = l_Lean_stringToMessageData(v___y_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___y_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__1);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_ofName(v_mod_1035_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_Name_isAnonymous(v_hint_1036_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__3);
v___x_1057_ = l_Lean_MessageData_ofName(v_hint_1036_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___y_1041_ = v___x_1054_;
v___y_1042_ = v___x_1058_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_hint_1036_);
v___x_1059_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___closed__5);
v___y_1041_ = v___x_1054_;
v___y_1042_ = v___x_1059_;
goto v___jp_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed(lean_object* v_modifyEnv_1072_, lean_object* v___f_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_cls_1078_, lean_object* v_toBind_1079_, lean_object* v___f_1080_, lean_object* v_mod_1081_, lean_object* v_hint_1082_, lean_object* v_isMeta_1083_, lean_object* v_isExporting_1084_, lean_object* v_____do__lift_1085_){
_start:
{
uint8_t v_isMeta_boxed_1086_; uint8_t v_isExporting_boxed_1087_; uint8_t v_____do__lift_562__boxed_1088_; lean_object* v_res_1089_; 
v_isMeta_boxed_1086_ = lean_unbox(v_isMeta_1083_);
v_isExporting_boxed_1087_ = lean_unbox(v_isExporting_1084_);
v_____do__lift_562__boxed_1088_ = lean_unbox(v_____do__lift_1085_);
v_res_1089_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4(v_modifyEnv_1072_, v___f_1073_, v_inst_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_cls_1078_, v_toBind_1079_, v___f_1080_, v_mod_1081_, v_hint_1082_, v_isMeta_boxed_1086_, v_isExporting_boxed_1087_, v_____do__lift_562__boxed_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v_entry_1093_, lean_object* v_inst_1094_, lean_object* v_modifyEnv_1095_, lean_object* v_inst_1096_, lean_object* v_toPure_1097_, lean_object* v_toBind_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_mod_1102_, lean_object* v_hint_1103_, uint8_t v_isMeta_1104_, uint8_t v_isExporting_1105_, lean_object* v_____do__lift_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1107_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1108_ = lean_box(1);
v___x_1109_ = lean_box(0);
v___x_1110_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1090_, v___x_1107_, v_____do__lift_1106_, v___x_1108_, v___x_1109_);
lean_inc_ref(v_entry_1093_);
v___x_1111_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1091_, v___x_1092_, v___x_1110_, v_entry_1093_);
if (v___x_1111_ == 0)
{
lean_object* v_getInheritedTraceOptions_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v_cls_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_getInheritedTraceOptions_1112_ = lean_ctor_get(v_inst_1094_, 2);
lean_inc(v_getInheritedTraceOptions_1112_);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1113_, 0, v___x_1107_);
lean_closure_set(v___f_1113_, 1, v_entry_1093_);
lean_closure_set(v___f_1113_, 2, v___x_1109_);
lean_inc_ref(v___f_1113_);
lean_inc(v_modifyEnv_1095_);
v___f_1114_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1114_, 0, v_modifyEnv_1095_);
lean_closure_set(v___f_1114_, 1, v___f_1113_);
v_cls_1115_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1098_, 3);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1116_, 0, v_inst_1096_);
lean_closure_set(v___f_1116_, 1, v_toPure_1097_);
lean_closure_set(v___f_1116_, 2, v_cls_1115_);
lean_closure_set(v___f_1116_, 3, v_toBind_1098_);
v___x_1117_ = lean_box(v_isMeta_1104_);
v___x_1118_ = lean_box(v_isExporting_1105_);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_1119_, 0, v_modifyEnv_1095_);
lean_closure_set(v___f_1119_, 1, v___f_1113_);
lean_closure_set(v___f_1119_, 2, v_inst_1099_);
lean_closure_set(v___f_1119_, 3, v_inst_1094_);
lean_closure_set(v___f_1119_, 4, v_inst_1100_);
lean_closure_set(v___f_1119_, 5, v_inst_1101_);
lean_closure_set(v___f_1119_, 6, v_cls_1115_);
lean_closure_set(v___f_1119_, 7, v_toBind_1098_);
lean_closure_set(v___f_1119_, 8, v___f_1114_);
lean_closure_set(v___f_1119_, 9, v_mod_1102_);
lean_closure_set(v___f_1119_, 10, v_hint_1103_);
lean_closure_set(v___f_1119_, 11, v___x_1117_);
lean_closure_set(v___f_1119_, 12, v___x_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1112_, v___f_1116_);
v___x_1121_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1120_, v___f_1119_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_hint_1103_);
lean_dec(v_mod_1102_);
lean_dec(v_inst_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
lean_dec(v_toBind_1098_);
lean_dec_ref(v_inst_1096_);
lean_dec(v_modifyEnv_1095_);
lean_dec_ref(v_inst_1094_);
lean_dec_ref(v_entry_1093_);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_apply_2(v_toPure_1097_, lean_box(0), v___x_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1124_ = _args[0];
lean_object* v___x_1125_ = _args[1];
lean_object* v___x_1126_ = _args[2];
lean_object* v_entry_1127_ = _args[3];
lean_object* v_inst_1128_ = _args[4];
lean_object* v_modifyEnv_1129_ = _args[5];
lean_object* v_inst_1130_ = _args[6];
lean_object* v_toPure_1131_ = _args[7];
lean_object* v_toBind_1132_ = _args[8];
lean_object* v_inst_1133_ = _args[9];
lean_object* v_inst_1134_ = _args[10];
lean_object* v_inst_1135_ = _args[11];
lean_object* v_mod_1136_ = _args[12];
lean_object* v_hint_1137_ = _args[13];
lean_object* v_isMeta_1138_ = _args[14];
lean_object* v_isExporting_1139_ = _args[15];
lean_object* v_____do__lift_1140_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1141_; uint8_t v_isExporting_boxed_1142_; lean_object* v_res_1143_; 
v_isMeta_boxed_1141_ = lean_unbox(v_isMeta_1138_);
v_isExporting_boxed_1142_ = lean_unbox(v_isExporting_1139_);
v_res_1143_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1(v___x_1124_, v___x_1125_, v___x_1126_, v_entry_1127_, v_inst_1128_, v_modifyEnv_1129_, v_inst_1130_, v_toPure_1131_, v_toBind_1132_, v_inst_1133_, v_inst_1134_, v_inst_1135_, v_mod_1136_, v_hint_1137_, v_isMeta_boxed_1141_, v_isExporting_boxed_1142_, v_____do__lift_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(lean_object* v_mod_1144_, uint8_t v_isMeta_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v_inst_1149_, lean_object* v_modifyEnv_1150_, lean_object* v_inst_1151_, lean_object* v_toPure_1152_, lean_object* v_toBind_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_hint_1157_, lean_object* v_getEnv_1158_, lean_object* v_____do__lift_1159_){
_start:
{
uint8_t v_isExporting_1160_; lean_object* v_entry_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; 
v_isExporting_1160_ = lean_ctor_get_uint8(v_____do__lift_1159_, sizeof(void*)*8);
lean_inc(v_mod_1144_);
v_entry_1161_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1161_, 0, v_mod_1144_);
lean_ctor_set_uint8(v_entry_1161_, sizeof(void*)*1, v_isExporting_1160_);
lean_ctor_set_uint8(v_entry_1161_, sizeof(void*)*1 + 1, v_isMeta_1145_);
v___x_1162_ = lean_box(v_isMeta_1145_);
v___x_1163_ = lean_box(v_isExporting_1160_);
lean_inc(v_toBind_1153_);
v___f_1164_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__1___boxed), 17, 16);
lean_closure_set(v___f_1164_, 0, v___x_1146_);
lean_closure_set(v___f_1164_, 1, v___x_1147_);
lean_closure_set(v___f_1164_, 2, v___x_1148_);
lean_closure_set(v___f_1164_, 3, v_entry_1161_);
lean_closure_set(v___f_1164_, 4, v_inst_1149_);
lean_closure_set(v___f_1164_, 5, v_modifyEnv_1150_);
lean_closure_set(v___f_1164_, 6, v_inst_1151_);
lean_closure_set(v___f_1164_, 7, v_toPure_1152_);
lean_closure_set(v___f_1164_, 8, v_toBind_1153_);
lean_closure_set(v___f_1164_, 9, v_inst_1154_);
lean_closure_set(v___f_1164_, 10, v_inst_1155_);
lean_closure_set(v___f_1164_, 11, v_inst_1156_);
lean_closure_set(v___f_1164_, 12, v_mod_1144_);
lean_closure_set(v___f_1164_, 13, v_hint_1157_);
lean_closure_set(v___f_1164_, 14, v___x_1162_);
lean_closure_set(v___f_1164_, 15, v___x_1163_);
v___x_1165_ = lean_apply_4(v_toBind_1153_, lean_box(0), lean_box(0), v_getEnv_1158_, v___f_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed(lean_object* v_mod_1166_, lean_object* v_isMeta_1167_, lean_object* v___x_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_inst_1171_, lean_object* v_modifyEnv_1172_, lean_object* v_inst_1173_, lean_object* v_toPure_1174_, lean_object* v_toBind_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_hint_1179_, lean_object* v_getEnv_1180_, lean_object* v_____do__lift_1181_){
_start:
{
uint8_t v_isMeta_boxed_1182_; lean_object* v_res_1183_; 
v_isMeta_boxed_1182_ = lean_unbox(v_isMeta_1167_);
v_res_1183_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2(v_mod_1166_, v_isMeta_boxed_1182_, v___x_1168_, v___x_1169_, v___x_1170_, v_inst_1171_, v_modifyEnv_1172_, v_inst_1173_, v_toPure_1174_, v_toBind_1175_, v_inst_1176_, v_inst_1177_, v_inst_1178_, v_hint_1179_, v_getEnv_1180_, v_____do__lift_1181_);
lean_dec_ref(v_____do__lift_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_mod_1190_, uint8_t v_isMeta_1191_, lean_object* v_hint_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_getEnv_1195_; lean_object* v_modifyEnv_1196_; lean_object* v_toPure_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1184_, 0);
v_toBind_1194_ = lean_ctor_get(v_inst_1184_, 1);
lean_inc_n(v_toBind_1194_, 2);
v_getEnv_1195_ = lean_ctor_get(v_inst_1185_, 0);
lean_inc_n(v_getEnv_1195_, 2);
v_modifyEnv_1196_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc(v_modifyEnv_1196_);
lean_dec_ref(v_inst_1185_);
v_toPure_1197_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1197_);
v___x_1198_ = ((lean_object*)(l_Lean_instBEqExtraModUse___closed__0));
v___x_1199_ = ((lean_object*)(l_Lean_instHashableExtraModUse___closed__0));
v___x_1200_ = lean_obj_once(&l_Lean_getExtraModUses___closed__0, &l_Lean_getExtraModUses___closed__0_once, _init_l_Lean_getExtraModUses___closed__0);
v___x_1201_ = lean_box(v_isMeta_1191_);
v___f_1202_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___lam__2___boxed), 16, 15);
lean_closure_set(v___f_1202_, 0, v_mod_1190_);
lean_closure_set(v___f_1202_, 1, v___x_1201_);
lean_closure_set(v___f_1202_, 2, v___x_1200_);
lean_closure_set(v___f_1202_, 3, v___x_1198_);
lean_closure_set(v___f_1202_, 4, v___x_1199_);
lean_closure_set(v___f_1202_, 5, v_inst_1186_);
lean_closure_set(v___f_1202_, 6, v_modifyEnv_1196_);
lean_closure_set(v___f_1202_, 7, v_inst_1187_);
lean_closure_set(v___f_1202_, 8, v_toPure_1197_);
lean_closure_set(v___f_1202_, 9, v_toBind_1194_);
lean_closure_set(v___f_1202_, 10, v_inst_1184_);
lean_closure_set(v___f_1202_, 11, v_inst_1188_);
lean_closure_set(v___f_1202_, 12, v_inst_1189_);
lean_closure_set(v___f_1202_, 13, v_hint_1192_);
lean_closure_set(v___f_1202_, 14, v_getEnv_1195_);
v___x_1203_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_getEnv_1195_, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg___boxed(lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_mod_1210_, lean_object* v_isMeta_1211_, lean_object* v_hint_1212_){
_start:
{
uint8_t v_isMeta_boxed_1213_; lean_object* v_res_1214_; 
v_isMeta_boxed_1213_ = lean_unbox(v_isMeta_1211_);
v_res_1214_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1204_, v_inst_1205_, v_inst_1206_, v_inst_1207_, v_inst_1208_, v_inst_1209_, v_mod_1210_, v_isMeta_boxed_1213_, v_hint_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_mod_1222_, uint8_t v_isMeta_1223_, lean_object* v_hint_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1216_, v_inst_1217_, v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_mod_1222_, v_isMeta_1223_, v_hint_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___boxed(lean_object* v_m_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_mod_1233_, lean_object* v_isMeta_1234_, lean_object* v_hint_1235_){
_start:
{
uint8_t v_isMeta_boxed_1236_; lean_object* v_res_1237_; 
v_isMeta_boxed_1236_ = lean_unbox(v_isMeta_1234_);
v_res_1237_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore(v_m_1226_, v_inst_1227_, v_inst_1228_, v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_mod_1233_, v_isMeta_boxed_1236_, v_hint_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0(lean_object* v_modName_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, uint8_t v_isMeta_1245_, lean_object* v_toPure_1246_, lean_object* v_____do__lift_1247_){
_start:
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = l_Lean_Environment_mainModule(v_____do__lift_1247_);
v___x_1249_ = lean_name_eq(v_modName_1238_, v___x_1248_);
lean_dec(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_toPure_1246_);
v___x_1250_ = lean_box(0);
v___x_1251_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_modName_1238_, v_isMeta_1245_, v___x_1250_);
return v___x_1251_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_inst_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec(v_modName_1238_);
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_apply_2(v_toPure_1246_, lean_box(0), v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___lam__0___boxed(lean_object* v_modName_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_isMeta_1261_, lean_object* v_toPure_1262_, lean_object* v_____do__lift_1263_){
_start:
{
uint8_t v_isMeta_boxed_1264_; lean_object* v_res_1265_; 
v_isMeta_boxed_1264_ = lean_unbox(v_isMeta_1261_);
v_res_1265_ = l_Lean_recordExtraModUse___redArg___lam__0(v_modName_1254_, v_inst_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_isMeta_boxed_1264_, v_toPure_1262_, v_____do__lift_1263_);
lean_dec_ref(v_____do__lift_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg(lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_modName_1272_, uint8_t v_isMeta_1273_){
_start:
{
lean_object* v_toApplicative_1274_; lean_object* v_toBind_1275_; lean_object* v_getEnv_1276_; lean_object* v_toPure_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; 
v_toApplicative_1274_ = lean_ctor_get(v_inst_1266_, 0);
v_toBind_1275_ = lean_ctor_get(v_inst_1266_, 1);
lean_inc(v_toBind_1275_);
v_getEnv_1276_ = lean_ctor_get(v_inst_1267_, 0);
lean_inc(v_getEnv_1276_);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1277_);
v___x_1278_ = lean_box(v_isMeta_1273_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUse___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_1279_, 0, v_modName_1272_);
lean_closure_set(v___f_1279_, 1, v_inst_1266_);
lean_closure_set(v___f_1279_, 2, v_inst_1267_);
lean_closure_set(v___f_1279_, 3, v_inst_1268_);
lean_closure_set(v___f_1279_, 4, v_inst_1269_);
lean_closure_set(v___f_1279_, 5, v_inst_1270_);
lean_closure_set(v___f_1279_, 6, v_inst_1271_);
lean_closure_set(v___f_1279_, 7, v___x_1278_);
lean_closure_set(v___f_1279_, 8, v_toPure_1277_);
v___x_1280_ = lean_apply_4(v_toBind_1275_, lean_box(0), lean_box(0), v_getEnv_1276_, v___f_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___redArg___boxed(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_modName_1287_, lean_object* v_isMeta_1288_){
_start:
{
uint8_t v_isMeta_boxed_1289_; lean_object* v_res_1290_; 
v_isMeta_boxed_1289_ = lean_unbox(v_isMeta_1288_);
v_res_1290_ = l_Lean_recordExtraModUse___redArg(v_inst_1281_, v_inst_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_modName_1287_, v_isMeta_boxed_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse(lean_object* v_m_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_modName_1298_, uint8_t v_isMeta_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_recordExtraModUse___redArg(v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_modName_1298_, v_isMeta_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUse___boxed(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_modName_1308_, lean_object* v_isMeta_1309_){
_start:
{
uint8_t v_isMeta_boxed_1310_; lean_object* v_res_1311_; 
v_isMeta_boxed_1310_ = lean_unbox(v_isMeta_1309_);
v_res_1311_ = l_Lean_recordExtraModUse(v_m_1301_, v_inst_1302_, v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v_modName_1308_, v_isMeta_boxed_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__0(lean_object* v_toPure_1312_, lean_object* v_____s_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_apply_2(v_toPure_1312_, lean_box(0), v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__1(lean_object* v___x_1316_, lean_object* v_toPure_1317_, lean_object* v_r_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1316_);
v___x_1320_ = lean_apply_2(v_toPure_1317_, lean_box(0), v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2(lean_object* v_env_1321_, lean_object* v___x_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_declName_1329_, lean_object* v_toBind_1330_, lean_object* v___f_1331_, lean_object* v_a_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v_modules_1336_; lean_object* v___x_1337_; lean_object* v_toImport_1338_; lean_object* v_module_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1335_ = l_Lean_Environment_header(v_env_1321_);
v_modules_1336_ = lean_ctor_get(v___x_1335_, 3);
lean_inc_ref(v_modules_1336_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_array_get(v___x_1322_, v_modules_1336_, v_a_1332_);
lean_dec_ref(v_modules_1336_);
v_toImport_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc_ref(v_toImport_1338_);
lean_dec(v___x_1337_);
v_module_1339_ = lean_ctor_get(v_toImport_1338_, 0);
lean_inc(v_module_1339_);
lean_dec_ref(v_toImport_1338_);
v___x_1340_ = 0;
v___x_1341_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_module_1339_, v___x_1340_, v_declName_1329_);
v___x_1342_ = lean_apply_4(v_toBind_1330_, lean_box(0), lean_box(0), v___x_1341_, v___f_1331_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed(lean_object* v_env_1343_, lean_object* v___x_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_declName_1351_, lean_object* v_toBind_1352_, lean_object* v___f_1353_, lean_object* v_a_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__2(v_env_1343_, v___x_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_declName_1351_, v_toBind_1352_, v___f_1353_, v_a_1354_, v_x_1355_, v___y_1356_);
lean_dec(v_a_1354_);
lean_dec_ref(v___x_1344_);
lean_dec_ref(v_env_1343_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__3(lean_object* v_toPure_1358_, lean_object* v_env_1359_, lean_object* v___x_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_declName_1367_, lean_object* v_toBind_1368_, lean_object* v___f_1369_, lean_object* v___x_1370_, lean_object* v___x_1371_, lean_object* v___x_1372_, lean_object* v_____r_1373_){
_start:
{
lean_object* v___y_1375_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1383_ = l_Lean_indirectModUseExt;
v___x_1384_ = lean_box(1);
v___x_1385_ = lean_box(0);
lean_inc_ref(v_env_1359_);
v___x_1386_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1370_, v___x_1383_, v_env_1359_, v___x_1384_, v___x_1385_);
lean_inc(v_declName_1367_);
v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1371_, v___x_1372_, v___x_1386_, v_declName_1367_);
lean_dec(v___x_1386_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2__spec__0_spec__2___lam__0___closed__0));
v___y_1375_ = v___x_1388_;
goto v___jp_1374_;
}
else
{
lean_object* v_val_1389_; 
v_val_1389_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1387_, 1);
v___y_1375_ = v_val_1389_;
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1376_ = lean_box(0);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
lean_closure_set(v___f_1377_, 1, v_toPure_1358_);
lean_inc(v_toBind_1368_);
lean_inc_ref(v_inst_1361_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__2___boxed), 14, 11);
lean_closure_set(v___f_1378_, 0, v_env_1359_);
lean_closure_set(v___f_1378_, 1, v___x_1360_);
lean_closure_set(v___f_1378_, 2, v_inst_1361_);
lean_closure_set(v___f_1378_, 3, v_inst_1362_);
lean_closure_set(v___f_1378_, 4, v_inst_1363_);
lean_closure_set(v___f_1378_, 5, v_inst_1364_);
lean_closure_set(v___f_1378_, 6, v_inst_1365_);
lean_closure_set(v___f_1378_, 7, v_inst_1366_);
lean_closure_set(v___f_1378_, 8, v_declName_1367_);
lean_closure_set(v___f_1378_, 9, v_toBind_1368_);
lean_closure_set(v___f_1378_, 10, v___f_1377_);
v_sz_1379_ = lean_array_size(v___y_1375_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1361_, v___y_1375_, v___f_1378_, v_sz_1379_, v___x_1380_, v___x_1376_);
v___x_1382_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v___x_1381_, v___f_1369_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4(lean_object* v___x_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_declName_1397_, lean_object* v_toBind_1398_, lean_object* v___f_1399_, uint8_t v_isMeta_1400_, lean_object* v_____do__lift_1401_){
_start:
{
uint8_t v___y_1403_; 
if (v_isMeta_1400_ == 0)
{
lean_dec_ref(v_____do__lift_1401_);
v___y_1403_ = v_isMeta_1400_;
goto v___jp_1402_;
}
else
{
uint8_t v___x_1408_; 
lean_inc(v_declName_1397_);
v___x_1408_ = l_Lean_isMarkedMeta(v_____do__lift_1401_, v_declName_1397_);
if (v___x_1408_ == 0)
{
v___y_1403_ = v_isMeta_1400_;
goto v___jp_1402_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = 0;
v___y_1403_ = v___x_1409_;
goto v___jp_1402_;
}
}
v___jp_1402_:
{
lean_object* v_toImport_1404_; lean_object* v_module_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_toImport_1404_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_ref(v_toImport_1404_);
lean_dec_ref(v___x_1390_);
v_module_1405_ = lean_ctor_get(v_toImport_1404_, 0);
lean_inc(v_module_1405_);
lean_dec_ref(v_toImport_1404_);
v___x_1406_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___redArg(v_inst_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_inst_1395_, v_inst_1396_, v_module_1405_, v___y_1403_, v_declName_1397_);
v___x_1407_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1406_, v___f_1399_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed(lean_object* v___x_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_declName_1417_, lean_object* v_toBind_1418_, lean_object* v___f_1419_, lean_object* v_isMeta_1420_, lean_object* v_____do__lift_1421_){
_start:
{
uint8_t v_isMeta_boxed_1422_; lean_object* v_res_1423_; 
v_isMeta_boxed_1422_ = lean_unbox(v_isMeta_1420_);
v_res_1423_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__4(v___x_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v_inst_1414_, v_inst_1415_, v_inst_1416_, v_declName_1417_, v_toBind_1418_, v___f_1419_, v_isMeta_boxed_1422_, v_____do__lift_1421_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5(lean_object* v_toPure_1424_, lean_object* v_declName_1425_, lean_object* v___x_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_toBind_1433_, lean_object* v___f_1434_, lean_object* v___x_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, uint8_t v_isMeta_1438_, lean_object* v_getEnv_1439_, lean_object* v_env_1440_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1440_, v_declName_1425_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref(v_env_1440_);
lean_dec(v_getEnv_1439_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec(v___f_1434_);
lean_dec(v_toBind_1433_);
lean_dec(v_inst_1432_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec_ref(v_inst_1427_);
lean_dec_ref(v___x_1426_);
lean_dec(v_declName_1425_);
goto v___jp_1441_;
}
else
{
lean_object* v_val_1445_; lean_object* v___x_1446_; lean_object* v_modules_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_val_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_val_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_Environment_header(v_env_1440_);
v_modules_1447_ = lean_ctor_get(v___x_1446_, 3);
lean_inc_ref(v_modules_1447_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = lean_array_get_size(v_modules_1447_);
v___x_1449_ = lean_nat_dec_lt(v_val_1445_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec_ref(v_modules_1447_);
lean_dec(v_val_1445_);
lean_dec_ref(v_env_1440_);
lean_dec(v_getEnv_1439_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec(v___f_1434_);
lean_dec(v_toBind_1433_);
lean_dec(v_inst_1432_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec_ref(v_inst_1427_);
lean_dec_ref(v___x_1426_);
lean_dec(v_declName_1425_);
goto v___jp_1441_;
}
else
{
lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
lean_inc_n(v_toBind_1433_, 2);
lean_inc(v_declName_1425_);
lean_inc(v_inst_1432_);
lean_inc_ref(v_inst_1431_);
lean_inc_ref(v_inst_1430_);
lean_inc_ref(v_inst_1429_);
lean_inc_ref(v_inst_1428_);
lean_inc_ref(v_inst_1427_);
v___f_1450_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__3), 16, 15);
lean_closure_set(v___f_1450_, 0, v_toPure_1424_);
lean_closure_set(v___f_1450_, 1, v_env_1440_);
lean_closure_set(v___f_1450_, 2, v___x_1426_);
lean_closure_set(v___f_1450_, 3, v_inst_1427_);
lean_closure_set(v___f_1450_, 4, v_inst_1428_);
lean_closure_set(v___f_1450_, 5, v_inst_1429_);
lean_closure_set(v___f_1450_, 6, v_inst_1430_);
lean_closure_set(v___f_1450_, 7, v_inst_1431_);
lean_closure_set(v___f_1450_, 8, v_inst_1432_);
lean_closure_set(v___f_1450_, 9, v_declName_1425_);
lean_closure_set(v___f_1450_, 10, v_toBind_1433_);
lean_closure_set(v___f_1450_, 11, v___f_1434_);
lean_closure_set(v___f_1450_, 12, v___x_1435_);
lean_closure_set(v___f_1450_, 13, v___x_1436_);
lean_closure_set(v___f_1450_, 14, v___x_1437_);
v___x_1451_ = lean_array_fget(v_modules_1447_, v_val_1445_);
lean_dec(v_val_1445_);
lean_dec_ref(v_modules_1447_);
v___x_1452_ = lean_box(v_isMeta_1438_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_1453_, 0, v___x_1451_);
lean_closure_set(v___f_1453_, 1, v_inst_1427_);
lean_closure_set(v___f_1453_, 2, v_inst_1428_);
lean_closure_set(v___f_1453_, 3, v_inst_1429_);
lean_closure_set(v___f_1453_, 4, v_inst_1430_);
lean_closure_set(v___f_1453_, 5, v_inst_1431_);
lean_closure_set(v___f_1453_, 6, v_inst_1432_);
lean_closure_set(v___f_1453_, 7, v_declName_1425_);
lean_closure_set(v___f_1453_, 8, v_toBind_1433_);
lean_closure_set(v___f_1453_, 9, v___f_1450_);
lean_closure_set(v___f_1453_, 10, v___x_1452_);
v___x_1454_ = lean_apply_4(v_toBind_1433_, lean_box(0), lean_box(0), v_getEnv_1439_, v___f_1453_);
return v___x_1454_;
}
}
v___jp_1441_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_apply_2(v_toPure_1424_, lean_box(0), v___x_1442_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toPure_1455_ = _args[0];
lean_object* v_declName_1456_ = _args[1];
lean_object* v___x_1457_ = _args[2];
lean_object* v_inst_1458_ = _args[3];
lean_object* v_inst_1459_ = _args[4];
lean_object* v_inst_1460_ = _args[5];
lean_object* v_inst_1461_ = _args[6];
lean_object* v_inst_1462_ = _args[7];
lean_object* v_inst_1463_ = _args[8];
lean_object* v_toBind_1464_ = _args[9];
lean_object* v___f_1465_ = _args[10];
lean_object* v___x_1466_ = _args[11];
lean_object* v___x_1467_ = _args[12];
lean_object* v___x_1468_ = _args[13];
lean_object* v_isMeta_1469_ = _args[14];
lean_object* v_getEnv_1470_ = _args[15];
lean_object* v_env_1471_ = _args[16];
_start:
{
uint8_t v_isMeta_boxed_1472_; lean_object* v_res_1473_; 
v_isMeta_boxed_1472_ = lean_unbox(v_isMeta_1469_);
v_res_1473_ = l_Lean_recordExtraModUseFromDecl___redArg___lam__5(v_toPure_1455_, v_declName_1456_, v___x_1457_, v_inst_1458_, v_inst_1459_, v_inst_1460_, v_inst_1461_, v_inst_1462_, v_inst_1463_, v_toBind_1464_, v___f_1465_, v___x_1466_, v___x_1467_, v___x_1468_, v_isMeta_boxed_1472_, v_getEnv_1470_, v_env_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_declName_1482_, uint8_t v_isMeta_1483_){
_start:
{
lean_object* v_toApplicative_1484_; lean_object* v_toBind_1485_; lean_object* v_getEnv_1486_; lean_object* v_toPure_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; 
v_toApplicative_1484_ = lean_ctor_get(v_inst_1476_, 0);
v_toBind_1485_ = lean_ctor_get(v_inst_1476_, 1);
lean_inc_n(v_toBind_1485_, 2);
v_getEnv_1486_ = lean_ctor_get(v_inst_1477_, 0);
lean_inc_n(v_getEnv_1486_, 2);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1484_, 1);
lean_inc_n(v_toPure_1487_, 2);
v___x_1488_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___redArg___closed__0));
v___x_1489_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___redArg___closed__1));
v___x_1490_ = lean_obj_once(&l_Lean_getIndirectModUses___closed__0, &l_Lean_getIndirectModUses___closed__0_once, _init_l_Lean_getIndirectModUses___closed__0);
v___x_1491_ = l_Lean_instInhabitedEffectiveImport_default;
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1492_, 0, v_toPure_1487_);
v___x_1493_ = lean_box(v_isMeta_1483_);
v___f_1494_ = lean_alloc_closure((void*)(l_Lean_recordExtraModUseFromDecl___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_1494_, 0, v_toPure_1487_);
lean_closure_set(v___f_1494_, 1, v_declName_1482_);
lean_closure_set(v___f_1494_, 2, v___x_1491_);
lean_closure_set(v___f_1494_, 3, v_inst_1476_);
lean_closure_set(v___f_1494_, 4, v_inst_1477_);
lean_closure_set(v___f_1494_, 5, v_inst_1478_);
lean_closure_set(v___f_1494_, 6, v_inst_1479_);
lean_closure_set(v___f_1494_, 7, v_inst_1480_);
lean_closure_set(v___f_1494_, 8, v_inst_1481_);
lean_closure_set(v___f_1494_, 9, v_toBind_1485_);
lean_closure_set(v___f_1494_, 10, v___f_1492_);
lean_closure_set(v___f_1494_, 11, v___x_1490_);
lean_closure_set(v___f_1494_, 12, v___x_1488_);
lean_closure_set(v___f_1494_, 13, v___x_1489_);
lean_closure_set(v___f_1494_, 14, v___x_1493_);
lean_closure_set(v___f_1494_, 15, v_getEnv_1486_);
v___x_1495_ = lean_apply_4(v_toBind_1485_, lean_box(0), lean_box(0), v_getEnv_1486_, v___f_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___redArg___boxed(lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_declName_1502_, lean_object* v_isMeta_1503_){
_start:
{
uint8_t v_isMeta_boxed_1504_; lean_object* v_res_1505_; 
v_isMeta_boxed_1504_ = lean_unbox(v_isMeta_1503_);
v_res_1505_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1496_, v_inst_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_declName_1502_, v_isMeta_boxed_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl(lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_declName_1513_, uint8_t v_isMeta_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_1507_, v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_declName_1513_, v_isMeta_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___boxed(lean_object* v_m_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_declName_1523_, lean_object* v_isMeta_1524_){
_start:
{
uint8_t v_isMeta_boxed_1525_; lean_object* v_res_1526_; 
v_isMeta_boxed_1525_ = lean_unbox(v_isMeta_1524_);
v_res_1526_ = l_Lean_recordExtraModUseFromDecl(v_m_1516_, v_inst_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_declName_1523_, v_isMeta_boxed_1525_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__0_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_s_1527_, lean_object* v_e_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_x_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_ExtraModUses_0__Lean_initFn___lam__1_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(v_x_1532_);
lean_dec_ref(v_x_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn___lam__2_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(lean_object* v_es_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_mk(v_es_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_));
v___x_1552_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2____boxed(lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
return v_res_1554_;
}
}
LEAN_EXPORT uint8_t l_Lean_isExtraRevModUse(lean_object* v_env_1558_, lean_object* v_modIdx_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1560_ = ((lean_object*)(l_Lean_isExtraRevModUse___closed__0));
v___x_1561_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1562_ = 0;
v___x_1563_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1560_, v___x_1561_, v_env_1558_, v_modIdx_1559_, v___x_1562_);
v___x_1564_ = lean_array_get_size(v___x_1563_);
lean_dec_ref(v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_nat_dec_eq(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
uint8_t v___x_1567_; 
v___x_1567_ = 1;
return v___x_1567_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = 0;
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isExtraRevModUse___boxed(lean_object* v_env_1569_, lean_object* v_modIdx_1570_){
_start:
{
uint8_t v_res_1571_; lean_object* v_r_1572_; 
v_res_1571_ = l_Lean_isExtraRevModUse(v_env_1569_, v_modIdx_1570_);
lean_dec(v_modIdx_1570_);
lean_dec_ref(v_env_1569_);
v_r_1572_ = lean_box(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0(lean_object* v___x_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v_toEnvExtension_1575_; lean_object* v_asyncMode_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_toEnvExtension_1575_ = lean_ctor_get(v___x_1573_, 0);
v_asyncMode_1576_ = lean_ctor_get(v_toEnvExtension_1575_, 2);
lean_inc(v_asyncMode_1576_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_box(0);
v___x_1579_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1573_, v_x_1574_, v___x_1577_, v_asyncMode_1576_, v___x_1578_);
lean_dec(v_asyncMode_1576_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__0));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(lean_object* v_modifyEnv_1583_, lean_object* v___f_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_cls_1589_, lean_object* v_toBind_1590_, lean_object* v___f_1591_, uint8_t v_____do__lift_1592_){
_start:
{
if (v_____do__lift_1592_ == 0)
{
lean_object* v___x_1593_; 
lean_dec(v___f_1591_);
lean_dec(v_toBind_1590_);
lean_dec(v_cls_1589_);
lean_dec(v_inst_1588_);
lean_dec_ref(v_inst_1587_);
lean_dec_ref(v_inst_1586_);
lean_dec_ref(v_inst_1585_);
v___x_1593_ = lean_apply_1(v_modifyEnv_1583_, v___f_1584_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v___f_1584_);
lean_dec(v_modifyEnv_1583_);
v___x_1594_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___closed__1);
v___x_1595_ = l_Lean_addTrace___redArg(v_inst_1585_, v_inst_1586_, v_inst_1587_, v_inst_1588_, v_cls_1589_, v___x_1594_);
v___x_1596_ = lean_apply_4(v_toBind_1590_, lean_box(0), lean_box(0), v___x_1595_, v___f_1591_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed(lean_object* v_modifyEnv_1597_, lean_object* v___f_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_cls_1603_, lean_object* v_toBind_1604_, lean_object* v___f_1605_, lean_object* v_____do__lift_1606_){
_start:
{
uint8_t v_____do__lift_188__boxed_1607_; lean_object* v_res_1608_; 
v_____do__lift_188__boxed_1607_ = lean_unbox(v_____do__lift_1606_);
v_res_1608_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4(v_modifyEnv_1597_, v___f_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_inst_1602_, v_cls_1603_, v_toBind_1604_, v___f_1605_, v_____do__lift_188__boxed_1607_);
return v_res_1608_;
}
}
static lean_object* _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___f_1610_; 
v___x_1609_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1610_, 0, v___x_1609_);
return v___f_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1(lean_object* v___x_1611_, lean_object* v_toPure_1612_, lean_object* v_inst_1613_, lean_object* v_modifyEnv_1614_, lean_object* v_inst_1615_, lean_object* v_toBind_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_____do__lift_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1621_ = l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt;
v___x_1622_ = lean_box(1);
v___x_1623_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1611_, v___x_1621_, v_____do__lift_1620_, v___x_1622_);
v___x_1624_ = l_List_isEmpty___redArg(v___x_1623_);
lean_dec(v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec(v_inst_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec_ref(v_inst_1617_);
lean_dec(v_toBind_1616_);
lean_dec_ref(v_inst_1615_);
lean_dec(v_modifyEnv_1614_);
lean_dec_ref(v_inst_1613_);
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_apply_2(v_toPure_1612_, lean_box(0), v___x_1625_);
return v___x_1626_;
}
else
{
lean_object* v_getInheritedTraceOptions_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v_cls_1630_; lean_object* v___f_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_getInheritedTraceOptions_1627_ = lean_ctor_get(v_inst_1613_, 2);
lean_inc(v_getInheritedTraceOptions_1627_);
v___f_1628_ = lean_obj_once(&l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0, &l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0_once, _init_l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1___closed__0);
lean_inc(v_modifyEnv_1614_);
v___f_1629_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1629_, 0, v_modifyEnv_1614_);
lean_closure_set(v___f_1629_, 1, v___f_1628_);
v_cls_1630_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
lean_inc_n(v_toBind_1616_, 3);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_recordIndirectModUse___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1631_, 0, v_inst_1615_);
lean_closure_set(v___f_1631_, 1, v_toPure_1612_);
lean_closure_set(v___f_1631_, 2, v_cls_1630_);
lean_closure_set(v___f_1631_, 3, v_toBind_1616_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1632_, 0, v_modifyEnv_1614_);
lean_closure_set(v___f_1632_, 1, v___f_1628_);
lean_closure_set(v___f_1632_, 2, v_inst_1617_);
lean_closure_set(v___f_1632_, 3, v_inst_1613_);
lean_closure_set(v___f_1632_, 4, v_inst_1618_);
lean_closure_set(v___f_1632_, 5, v_inst_1619_);
lean_closure_set(v___f_1632_, 6, v_cls_1630_);
lean_closure_set(v___f_1632_, 7, v_toBind_1616_);
lean_closure_set(v___f_1632_, 8, v___f_1629_);
v___x_1633_ = lean_apply_4(v_toBind_1616_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1627_, v___f_1631_);
v___x_1634_ = lean_apply_4(v_toBind_1616_, lean_box(0), lean_box(0), v___x_1633_, v___f_1632_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule___redArg(lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_){
_start:
{
lean_object* v_toApplicative_1641_; lean_object* v_toBind_1642_; lean_object* v_getEnv_1643_; lean_object* v_modifyEnv_1644_; lean_object* v_toPure_1645_; lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; 
v_toApplicative_1641_ = lean_ctor_get(v_inst_1635_, 0);
v_toBind_1642_ = lean_ctor_get(v_inst_1635_, 1);
lean_inc_n(v_toBind_1642_, 2);
v_getEnv_1643_ = lean_ctor_get(v_inst_1636_, 0);
lean_inc(v_getEnv_1643_);
v_modifyEnv_1644_ = lean_ctor_get(v_inst_1636_, 1);
lean_inc(v_modifyEnv_1644_);
lean_dec_ref(v_inst_1636_);
v_toPure_1645_ = lean_ctor_get(v_toApplicative_1641_, 1);
lean_inc(v_toPure_1645_);
v___x_1646_ = lean_box(0);
v___f_1647_ = lean_alloc_closure((void*)(l_Lean_recordExtraRevUseOfCurrentModule___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1647_, 0, v___x_1646_);
lean_closure_set(v___f_1647_, 1, v_toPure_1645_);
lean_closure_set(v___f_1647_, 2, v_inst_1637_);
lean_closure_set(v___f_1647_, 3, v_modifyEnv_1644_);
lean_closure_set(v___f_1647_, 4, v_inst_1638_);
lean_closure_set(v___f_1647_, 5, v_toBind_1642_);
lean_closure_set(v___f_1647_, 6, v_inst_1635_);
lean_closure_set(v___f_1647_, 7, v_inst_1639_);
lean_closure_set(v___f_1647_, 8, v_inst_1640_);
v___x_1648_ = lean_apply_4(v_toBind_1642_, lean_box(0), lean_box(0), v_getEnv_1643_, v___f_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraRevUseOfCurrentModule(lean_object* v_m_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_recordExtraRevUseOfCurrentModule___redArg(v_inst_1650_, v_inst_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_, v_inst_1655_);
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(4259277863u);
v___x_1672_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__5_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1673_ = l_Lean_Name_num___override(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__7_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1676_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__6_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1677_ = l_Lean_Name_str___override(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_initFn___closed__9_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_));
v___x_1680_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__8_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1681_ = l_Lean_Name_str___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_unsigned_to_nat(2u);
v___x_1683_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__10_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1684_ = l_Lean_Name_num___override(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1686_ = ((lean_object*)(l_Lean_recordIndirectModUse___redArg___lam__5___closed__1));
v___x_1687_ = 0;
v___x_1688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_, &l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2__once, _init_l___private_Lean_ExtraModUses_0__Lean_initFn___closed__11_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_);
v___x_1689_ = l_Lean_registerTraceClass(v___x_1686_, v___x_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2____boxed(lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
return v_res_1691_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_1766255300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_indirectModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_indirectModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_231983239____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_extraModUses = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_extraModUses);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_2233475121____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_isExtraRevModUseExt);
lean_dec_ref(res);
res = l___private_Lean_ExtraModUses_0__Lean_initFn_00___x40_Lean_ExtraModUses_4259277863____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ExtraModUses(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ExtraModUses(builtin);
}
#ifdef __cplusplus
}
#endif
