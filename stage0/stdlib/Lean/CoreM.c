// Lean compiler output
// Module: Lean.CoreM
// Imports: public import Lean.Util.RecDepth public import Lean.ResolveName public import Lean.Language.Basic import Init.While import Lean.Compiler.MetaAttr import Lean.Util.ForEachExpr
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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diagnostics"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(236, 43, 109, 94, 169, 251, 160, 225)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "collect diagnostic information"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(85, 175, 193, 127, 103, 176, 3, 141)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(236, 43, 109, 94, 169, 251, 160, 225)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 127, 68, 246, 163, 120, 127, 117)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "only diagnostic counters above this threshold are reported by the definitional equality"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(85, 175, 193, 127, 103, 176, 3, 141)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(189, 224, 169, 251, 54, 90, 86, 210)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics_threshold;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "maxHeartbeats"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 202, 216, 251, 148, 187, 135, 206)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 127, .m_capacity = 127, .m_length = 126, .m_data = "maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(200000) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 134, 20, 158, 154, 92, 25, 244)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxHeartbeats;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "async"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 0, 36, 68, 138, 2, 151, 20)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 549, .m_capacity = 549, .m_length = 548, .m_data = "perform elaboration using multiple threads where possible\n\nThis option defaults to `false` but (when not explicitly set) is overridden to `true` in the Lean language server and cmdline. Metaprogramming users driving elaboration directly via e.g. `Lean.Elab.Command.elabCommandTopLevel` can opt into asynchronous elaboration by setting this option but then are responsible for processing messages and other data not only in the resulting command state but also from async tasks in `Lean.Command.Context.snap\?` and `Lean.Command.State.snapshotTasks`."};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 142, 149, 180, 91, 16, 128, 108)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_async;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inServer"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 240, 154, 175, 204, 241, 45, 132)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 142, .m_capacity = 142, .m_length = 141, .m_data = "true if elaboration is being run inside the Lean language server\n\nThis option is set by the file worker and should not be modified otherwise."};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 229, 98, 36, 235, 0, 44, 230)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_inServer;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "internal"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cmdlineSnapshots"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 49, 45, 44, 152, 148, 209, 41)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(129, 168, 39, 157, 17, 55, 119, 69)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "reduce information stored in snapshots to the minimum necessary for the cmdline driver: diagnostics per command and final full snapshot"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(144, 169, 153, 11, 83, 41, 70, 160)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(76, 4, 69, 69, 104, 72, 39, 244)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_internal_cmdlineSnapshots;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_useDiagnosticMsg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "(invalid MessageData.lazy, missing context)"};
static const lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__0 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_useDiagnosticMsg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_useDiagnosticMsg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__1 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__0___closed__1_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object*);
static const lean_string_object l_Lean_useDiagnosticMsg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Additional diagnostic information may be available using the `set_option "};
static const lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__0 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__2___closed__0_value;
static const lean_string_object l_Lean_useDiagnosticMsg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " true` command."};
static const lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__1 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__2___closed__1_value;
static const lean_string_object l_Lean_useDiagnosticMsg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__2 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_useDiagnosticMsg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_useDiagnosticMsg___lam__2___closed__2_value)}};
static const lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__3 = (const lean_object*)&l_Lean_useDiagnosticMsg___lam__2___closed__3_value;
static lean_object* l_Lean_useDiagnosticMsg___lam__2___closed__4;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_useDiagnosticMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_useDiagnosticMsg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_useDiagnosticMsg___closed__0 = (const lean_object*)&l_Lean_useDiagnosticMsg___closed__0_value;
static const lean_closure_object l_Lean_useDiagnosticMsg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_useDiagnosticMsg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_useDiagnosticMsg___closed__1 = (const lean_object*)&l_Lean_useDiagnosticMsg___closed__1_value;
static const lean_closure_object l_Lean_useDiagnosticMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_useDiagnosticMsg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_useDiagnosticMsg___closed__2 = (const lean_object*)&l_Lean_useDiagnosticMsg___closed__2_value;
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_useDiagnosticMsg___closed__3;
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg;
static const lean_ctor_object l_Lean_instInhabitedDeclNameGenerator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedDeclNameGenerator_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedDeclNameGenerator_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDeclNameGenerator_default = (const lean_object*)&l_Lean_instInhabitedDeclNameGenerator_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDeclNameGenerator = (const lean_object*)&l_Lean_instInhabitedDeclNameGenerator_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_next(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkChild(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_withDeclNameForAuxNaming___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withDeclNameForAuxNaming___redArg___closed__0 = (const lean_object*)&l_Lean_withDeclNameForAuxNaming___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Kernel"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 59, 86, 63, 192, 192, 9, 44)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "CoreM"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 217, 218, 0, 248, 59, 21, 64)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__6_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(86, 231, 131, 141, 18, 25, 135, 2)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__7_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(255, 20, 15, 255, 19, 62, 230, 247)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Core"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 65, 12, 204, 168, 72, 213, 104)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__10_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 48, 25, 9, 246, 74, 120, 153)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__12_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 142, 56, 95, 209, 8, 154, 178)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__14_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(50, 168, 0, 93, 247, 80, 64, 217)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__15_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 151, 68, 77, 1, 54, 255, 115)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_CoreM_0__Lean_Core_initFn___closed__20_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__20_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__20_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
static lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instInhabitedCache_default___closed__0;
static lean_object* l_Lean_Core_instInhabitedCache_default___closed__1;
static lean_object* l_Lean_Core_instInhabitedCache_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache_default;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Core_instMonadCoreM___closed__1;
static const lean_closure_object l_Lean_Core_instMonadCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadCoreM___closed__2_value;
static const lean_closure_object l_Lean_Core_instMonadCoreM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadCoreM___closed__3 = (const lean_object*)&l_Lean_Core_instMonadCoreM___closed__3_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
extern lean_object* l_Lean_instInhabitedMessageData_default;
static lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instInhabitedCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instInhabitedCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instInhabitedCoreM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadRefCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadRefCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadRefCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadRefCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadRefCoreM___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadRefCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadRefCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadRefCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadRefCoreM = (const lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__2_value;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadEnvCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadEnvCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadEnvCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadEnvCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadEnvCoreM___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadEnvCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadEnvCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadEnvCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadEnvCoreM = (const lean_object*)&l_Lean_Core_instMonadEnvCoreM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadOptionsCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadOptionsCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadOptionsCoreM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadOptionsCoreM = (const lean_object*)&l_Lean_Core_instMonadOptionsCoreM___closed__0_value;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
extern lean_object* l_Lean_KVMap_instValueBool;
static lean_object* l_Lean_Core_instMonadWithOptionsCoreM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadNameGeneratorCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadNameGeneratorCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadNameGeneratorCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadNameGeneratorCoreM = (const lean_object*)&l_Lean_Core_instMonadNameGeneratorCoreM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM = (const lean_object*)&l_Lean_Core_instMonadDeclNameGeneratorCoreM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadRecDepthCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadRecDepthCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__1_value;
static const lean_closure_object l_Lean_Core_instMonadRecDepthCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__2_value;
static const lean_ctor_object l_Lean_Core_instMonadRecDepthCoreM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__1_value),((lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__2_value)}};
static const lean_object* l_Lean_Core_instMonadRecDepthCoreM___closed__3 = (const lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadRecDepthCoreM = (const lean_object*)&l_Lean_Core_instMonadRecDepthCoreM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadResolveNameCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadResolveNameCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadResolveNameCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadResolveNameCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadResolveNameCoreM = (const lean_object*)&l_Lean_Core_instMonadResolveNameCoreM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadQuotationCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadQuotationCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__1_value;
static const lean_closure_object l_Lean_Core_instMonadQuotationCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_withFreshMacroScope___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__2_value;
static const lean_ctor_object l_Lean_Core_instMonadQuotationCoreM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__2_value),((lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__1_value),((lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__2_value)}};
static const lean_object* l_Lean_Core_instMonadQuotationCoreM___closed__3 = (const lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadQuotationCoreM = (const lean_object*)&l_Lean_Core_instMonadQuotationCoreM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadInfoTreeCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadInfoTreeCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__1_value;
static const lean_ctor_object l_Lean_Core_instMonadInfoTreeCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__1_value)}};
static const lean_object* l_Lean_Core_instMonadInfoTreeCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadInfoTreeCoreM = (const lean_object*)&l_Lean_Core_instMonadInfoTreeCoreM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_instantiateValueLevelParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Not a definition or theorem: "};
static const lean_object* l_Lean_Core_instantiateValueLevelParams___closed__0 = (const lean_object*)&l_Lean_Core_instantiateValueLevelParams___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Core_instantiateValueLevelParams___closed__1;
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadLiftIOCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadLiftIOCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadLiftIOCoreM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadLiftIOCoreM = (const lean_object*)&l_Lean_Core_instMonadLiftIOCoreM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadTraceCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadTraceCoreM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadTraceCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadTraceCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadTraceCoreM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadTraceCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__1_value;
static const lean_closure_object l_Lean_Core_instMonadTraceCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadTraceCoreM___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadTraceCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__2_value;
static const lean_ctor_object l_Lean_Core_instMonadTraceCoreM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__1_value),((lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__2_value)}};
static const lean_object* l_Lean_Core_instMonadTraceCoreM___closed__3 = (const lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadTraceCoreM = (const lean_object*)&l_Lean_Core_instMonadTraceCoreM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_addHeartbeats(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_CoreM_toIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Core_CoreM_toIO___redArg___closed__0 = (const lean_object*)&l_Lean_Core_CoreM_toIO___redArg___closed__0_value;
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__0;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__1;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__2;
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__3;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__4;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__5;
static lean_object* l_Lean_Core_withIncRecDepth___redArg___closed__6;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "moduleNameAtTimeout"};
static const lean_object* l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(91, 236, 136, 192, 29, 215, 115, 61)}};
static const lean_object* l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 141, .m_capacity = 141, .m_length = 140, .m_data = "include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite"};
static const lean_object* l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value;
static lean_object* l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 126, 120, 188, 150, 235, 117, 203)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 253, 82, 155, 235, 136, 248, 216)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 32, 56, 99, 199, 19, 236, 231)}};
static const lean_object* l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_debug_moduleNameAtTimeout;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__0 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(134, 231, 82, 1, 7, 16, 116, 36)}};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__1 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__1_value;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "(deterministic) timeout"};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__2 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__2_value;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ", maximum number of heartbeats ("};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__4 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__4_value;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__5;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ") has been reached"};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__6 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__6_value;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__7;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Use `set_option "};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__8 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__8_value;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " <num>` to set the limit."};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__10 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__10_value;
static lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " at `"};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__12 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__12_value;
static const lean_string_object l_Lean_Core_throwMaxHeartbeat___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___closed__13 = (const lean_object*)&l_Lean_Core_throwMaxHeartbeat___redArg___closed__13_value;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__0;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__1;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__2;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Core_resetMessageLog___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__0 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__0_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__1 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__1_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__2 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__2_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__3 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__3_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__4 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__4_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__5 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__5_value;
static const lean_string_object l_Lean_Core_instMonadLogCoreM___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___closed__6 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__6_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_instMonadLogCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadLogCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadLogCoreM___closed__0 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__0_value;
static const lean_closure_object l_Lean_Core_instMonadLogCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadLogCoreM___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadLogCoreM___closed__1 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__1_value;
static const lean_closure_object l_Lean_Core_instMonadLogCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadLogCoreM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadLogCoreM___closed__2 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__2_value;
static const lean_closure_object l_Lean_Core_instMonadLogCoreM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadLogCoreM___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_instMonadLogCoreM___closed__3 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__3_value;
static const lean_ctor_object l_Lean_Core_instMonadLogCoreM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadRefCoreM___closed__0_value),((lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__1_value),((lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__2_value),((lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__3_value)}};
static const lean_object* l_Lean_Core_instMonadLogCoreM___closed__4 = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Core_instMonadLogCoreM = (const lean_object*)&l_Lean_Core_instMonadLogCoreM___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "stderrAsMessages"};
static const lean_object* l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 28, 29, 2, 125, 225, 175, 132)}};
static const lean_object* l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"};
static const lean_object* l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value;
static lean_object* l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__9_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 126, 120, 188, 150, 235, 117, 203)}};
static const lean_ctor_object l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Core_initFn___closed__0_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(35, 125, 57, 169, 199, 156, 160, 209)}};
static const lean_object* l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_stderrAsMessages;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__1 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__4 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__6 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__7 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__7_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__8 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__12 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__12_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__13 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__13_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__15 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16_value;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__17 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__17_value;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__22 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__22_value;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24;
static const lean_string_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27;
static const lean_ctor_object l_Lean_Core_mkSnapshot_x3f___auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(47, 79, 177, 134, 210, 33, 7, 227)}};
static const lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__28 = (const lean_object*)&l_Lean_Core_mkSnapshot_x3f___auto__1___closed__28_value;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38;
static lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39;
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot_x3f___auto__1;
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___auto__1;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Core_instMonadLogCoreM___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0_value;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0;
static lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
extern lean_object* l_Lean_trace_profiler_output;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__0_value;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__2;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
static double l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint64_t lean_io_get_tid();
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__18(lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__1 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__1_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__2 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__2_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__3 = (const lean_object*)&l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotLeaf_default;
static lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
extern lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqInternalExceptionId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_catchInternalIds___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqInternalExceptionId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_catchInternalIds___redArg___closed__0 = (const lean_object*)&l_Lean_catchInternalIds___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
static const lean_string_object l_Lean_mkArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_mkArrow___closed__0 = (const lean_object*)&l_Lean_mkArrow___closed__0_value;
static const lean_ctor_object l_Lean_mkArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_mkArrow___closed__1 = (const lean_object*)&l_Lean_mkArrow___closed__1_value;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Empty"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 106, 251, 72, 254, 34, 118, 241)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value),LEAN_SCALAR_PTR_LITERAL(122, 221, 252, 198, 56, 59, 37, 193)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__6_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "recOn"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__9_value),LEAN_SCALAR_PTR_LITERAL(207, 56, 58, 111, 136, 71, 194, 11)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value),LEAN_SCALAR_PTR_LITERAL(250, 240, 184, 175, 50, 245, 157, 81)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value),LEAN_SCALAR_PTR_LITERAL(214, 82, 43, 49, 91, 105, 112, 84)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value),LEAN_SCALAR_PTR_LITERAL(124, 240, 73, 14, 85, 121, 218, 187)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14_value;
static const lean_string_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__1_value),LEAN_SCALAR_PTR_LITERAL(192, 86, 186, 46, 229, 41, 245, 36)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16_value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17_value_aux_0),((lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__11_value),LEAN_SCALAR_PTR_LITERAL(156, 172, 111, 8, 9, 170, 133, 121)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17_value;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
static lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors;
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "code generator does not support recursor `"};
static const lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0_value;
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
static const lean_string_object l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "` yet, consider using `match ... with` and/or structural recursion"};
static const lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2_value;
static lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0 = (const lean_object*)&l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_traceBlock___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "blocked"};
static const lean_object* l_Lean_traceBlock___redArg___closed__0 = (const lean_object*)&l_Lean_traceBlock___redArg___closed__0_value;
static const lean_string_object l_Lean_traceBlock___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_Lean_traceBlock___redArg___closed__1 = (const lean_object*)&l_Lean_traceBlock___redArg___closed__1_value;
static const lean_ctor_object l_Lean_traceBlock___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_traceBlock___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_traceBlock___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_traceBlock___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 203, 205, 48, 20, 104, 179, 229)}};
static const lean_object* l_Lean_traceBlock___redArg___closed__2 = (const lean_object*)&l_Lean_traceBlock___redArg___closed__2_value;
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "postponeCompile"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 185, 42, 124, 107, 137, 69, 56)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 231, 88, 186, 170, 51, 115, 241)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 239, 65, 252, 111, 78, 125, 251)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compiler_postponeCompile;
LEAN_EXPORT uint8_t l_Lean_instBEqPostponedCompileDecl_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPostponedCompileDecl_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqPostponedCompileDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPostponedCompileDecl_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqPostponedCompileDecl___closed__0 = (const lean_object*)&l_Lean_instBEqPostponedCompileDecl___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqPostponedCompileDecl = (const lean_object*)&l_Lean_instBEqPostponedCompileDecl___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashablePostponedCompileDecl_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePostponedCompileDecl_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashablePostponedCompileDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePostponedCompileDecl_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashablePostponedCompileDecl___closed__0 = (const lean_object*)&l_Lean_instHashablePostponedCompileDecl___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashablePostponedCompileDecl = (const lean_object*)&l_Lean_instHashablePostponedCompileDecl___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "postponedCompileDeclsExt"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 92, 183, 123, 107, 182, 66, 103)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__6_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__7_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__8_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2__value;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_postponedCompileDeclsExt;
static const lean_string_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "call to compileDecls with uninitialized compileDeclsRef"};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2__value;
static lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsRef;
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_compileDecls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_compileDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 41, 138, 221, 159, 52, 80, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "postponing compilation of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__3_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_compileDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "compiler env"};
static const lean_object* l_Lean_compileDecls___closed__0 = (const lean_object*)&l_Lean_compileDecls___closed__0_value;
static const lean_string_object l_Lean_compileDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "compileDecls"};
static const lean_object* l_Lean_compileDecls___closed__1 = (const lean_object*)&l_Lean_compileDecls___closed__1_value;
static const lean_ctor_object l_Lean_compileDecls___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_compileDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_compileDecls___closed__2_value_aux_0),((lean_object*)&l_Lean_compileDecls___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 234, 115, 95, 204, 38, 204, 143)}};
static const lean_object* l_Lean_compileDecls___closed__2 = (const lean_object*)&l_Lean_compileDecls___closed__2_value;
lean_object* l_Lean_Environment_promiseChecked(lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__0;
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__1;
static const lean_string_object l_Lean_ImportM_runCoreM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_ImportM_runCoreM___redArg___closed__2 = (const lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__2_value;
static const lean_ctor_object l_Lean_ImportM_runCoreM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_ImportM_runCoreM___redArg___closed__3 = (const lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__3_value;
static const lean_ctor_object l_Lean_ImportM_runCoreM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ImportM_runCoreM___redArg___closed__4 = (const lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__4_value;
static const lean_ctor_object l_Lean_ImportM_runCoreM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ImportM_runCoreM___redArg___closed__5 = (const lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__5_value;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__6;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__7;
static const lean_string_object l_Lean_ImportM_runCoreM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<ImportM>"};
static const lean_object* l_Lean_ImportM_runCoreM___redArg___closed__8 = (const lean_object*)&l_Lean_ImportM_runCoreM___redArg___closed__8_value;
extern lean_object* l_Lean_Options_empty;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__9;
static uint8_t l_Lean_ImportM_runCoreM___redArg___closed__10;
static lean_object* l_Lean_ImportM_runCoreM___redArg___closed__11;
extern lean_object* l_Lean_instInhabitedFileMap_default;
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadExceptOfExceptionCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__0 = (const lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__0_value;
static const lean_closure_object l_Lean_instMonadExceptOfExceptionCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_tryCatch___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__1 = (const lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__1_value;
static const lean_ctor_object l_Lean_instMonadExceptOfExceptionCoreM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__0_value),((lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__1_value)}};
static const lean_object* l_Lean_instMonadExceptOfExceptionCoreM___closed__2 = (const lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadExceptOfExceptionCoreM = (const lean_object*)&l_Lean_instMonadExceptOfExceptionCoreM___closed__2_value;
static const lean_closure_object l_Lean_instMonadRuntimeExceptionCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_tryCatchRuntimeEx___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadRuntimeExceptionCoreM___closed__0 = (const lean_object*)&l_Lean_instMonadRuntimeExceptionCoreM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadRuntimeExceptionCoreM = (const lean_object*)&l_Lean_instMonadRuntimeExceptionCoreM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__0_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__8_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__11_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 100, 197, 9, 79, 238, 80, 109)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__0_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__0_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__1_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__0_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__13_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 184, 206, 165, 34, 33, 56, 118)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__1_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__1_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__2_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__1_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(114, 234, 213, 106, 254, 78, 198, 96)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__2_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__2_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__3_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__2_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 146, 141, 134, 213, 7, 123, 230)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__3_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__3_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__4_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__3_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)(((size_t)(660971656) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(196, 120, 190, 48, 3, 129, 62, 224)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__4_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__4_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__5_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__4_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 174, 239, 158, 51, 29, 5, 44)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__5_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__5_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__6_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__5_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_CoreM_0__Lean_Core_initFn___closed__20_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 161, 229, 143, 5, 131, 182, 4)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__6_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__6_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_CoreM_0__Lean_initFn___closed__7_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__6_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(126, 142, 237, 105, 124, 6, 16, 173)}};
static const lean_object* l___private_Lean_CoreM_0__Lean_initFn___closed__7_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_CoreM_0__Lean_initFn___closed__7_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 0, 1);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, 0, x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_19);
lean_inc(x_1);
x_23 = lean_register_option(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_24 = x_23;
} else {
 lean_dec_ref(x_23);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_18);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
lean_inc(x_1);
x_21 = lean_register_option(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__0___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__0___closed__2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__1(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_diagnostics;
x_5 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__0));
x_8 = 1;
x_9 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = l_Lean_MessageData_hint_x27(x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_useDiagnosticMsg___lam__2___closed__4;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__2(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_useDiagnosticMsg___closed__0));
x_2 = ((lean_object*)(l_Lean_useDiagnosticMsg___closed__1));
x_3 = ((lean_object*)(l_Lean_useDiagnosticMsg___closed__2));
x_4 = l_Lean_MessageData_lazy(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_useDiagnosticMsg___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_9 = 0;
lean_inc_ref(x_1);
x_10 = l_Lean_Environment_setExporting(x_1, x_9);
x_11 = l_Lean_Environment_containsOnBranch(x_10, x_2);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isPrivateName(x_2);
if (x_12 == 0)
{
x_3 = x_12;
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
x_13 = l_Lean_Environment_setExporting(x_1, x_11);
lean_inc(x_2);
x_14 = l_Lean_privateToUserName(x_2);
x_15 = l_Lean_Environment_containsOnBranch(x_13, x_14);
lean_dec(x_14);
x_3 = x_15;
goto block_8;
}
}
else
{
x_3 = x_11;
goto block_8;
}
block_8:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_isPrivateName(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_1);
x_5 = l_Lean_Environment_setExporting(x_1, x_3);
x_6 = l_Lean_mkPrivateName(x_1, x_2);
lean_dec_ref(x_1);
x_7 = l_Lean_Environment_containsOnBranch(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_name_append_index_after(x_4, x_8);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0_spec__0(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Environment_header(x_1);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 4);
lean_dec_ref(x_4);
x_6 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_idxs(x_2);
x_7 = l_List_foldrTR___at___00__private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr_spec__0(x_3, x_6);
if (x_5 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_isPrivateName(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_mkPrivateName(x_1, x_7);
return x_10;
}
else
{
return x_7;
}
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_DeclNameGenerator_mkUniqueName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_3, x_2);
lean_inc_ref(x_1);
x_5 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_isConflict(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_DeclNameGenerator_next(x_3);
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_11; uint8_t x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Name_hasMacroScopes(x_4);
if (x_14 == 0)
{
x_11 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Name_hasMacroScopes(x_3);
x_11 = x_15;
goto block_13;
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_6 = l_Lean_Name_append(x_4, x_5);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_DeclNameGenerator_mkUniqueName_spec__0(x_1, x_6, x_2);
x_8 = l___private_Lean_CoreM_0__Lean_DeclNameGenerator_mkUniqueName_curr(x_1, x_7, x_6);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_13:
{
if (x_11 == 0)
{
x_5 = x_3;
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = lean_erase_macro_scopes(x_3);
x_5 = x_12;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DeclNameGenerator_mkChild(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_inc(x_3);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
x_8 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadDeclNameGeneratorOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instMonadDeclNameGeneratorOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_DeclNameGenerator_mkUniqueName(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_apply_1(x_4, x_9);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__1), 6, 5);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_mkAuxDeclName___redArg___lam__2), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxDeclName___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withDeclNameForAuxNaming___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withDeclNameForAuxNaming___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withDeclNameForAuxNaming___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_name_eq(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_3);
x_17 = lean_apply_1(x_3, x_16);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_5);
x_19 = lean_apply_1(x_3, x_9);
x_20 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_20);
x_22 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_7, x_21);
return x_22;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withDeclNameForAuxNaming___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = ((lean_object*)(l_Lean_withDeclNameForAuxNaming___redArg___closed__0));
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withDeclNameForAuxNaming___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_2);
lean_closure_set(x_12, 6, x_10);
lean_closure_set(x_12, 7, x_5);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withDeclNameForAuxNaming___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3777671385u);
x_2 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__16_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__18_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_));
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__20_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_));
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_));
x_3 = 0;
x_4 = l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_maxHeartbeats;
x_3 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_1, x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instInhabitedCache_default___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instInhabitedCache_default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instInhabitedCache_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instMonadCoreM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_4(x_4, x_9, x_5, x_6, lean_box(0));
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_instMonadCoreM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_12 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_6);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_8);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_7);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_17);
lean_ctor_set(x_3, 2, x_18);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_23 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_24 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_19);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_25, 0, x_19);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_39 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedMessageData_default;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Core_instInhabitedCoreM___lam__0___closed__0;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instInhabitedCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Core_instInhabitedCoreM___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRefCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 5);
lean_dec(x_8);
lean_ctor_set(x_4, 5, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
x_18 = lean_ctor_get(x_4, 9);
x_19 = lean_ctor_get(x_4, 10);
x_20 = lean_ctor_get(x_4, 11);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
x_22 = lean_ctor_get(x_4, 12);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*14 + 1);
x_24 = lean_ctor_get(x_4, 13);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_2);
lean_ctor_set(x_25, 6, x_15);
lean_ctor_set(x_25, 7, x_16);
lean_ctor_set(x_25, 8, x_17);
lean_ctor_set(x_25, 9, x_18);
lean_ctor_set(x_25, 10, x_19);
lean_ctor_set(x_25, 11, x_20);
lean_ctor_set(x_25, 12, x_22);
lean_ctor_set(x_25, 13, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*14, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*14 + 1, x_23);
x_26 = lean_apply_3(x_3, x_25, x_5, lean_box(0));
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instMonadRefCoreM___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadEnvCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 5);
lean_dec(x_8);
x_9 = lean_apply_1(x_1, x_7);
x_10 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_5, 5, x_10);
lean_ctor_set(x_5, 0, x_9);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 2);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 6);
x_20 = lean_ctor_get(x_5, 7);
x_21 = lean_ctor_get(x_5, 8);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_22 = lean_apply_1(x_1, x_14);
x_23 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_24, 6, x_19);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_21);
x_25 = lean_st_ref_set(x_3, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadEnvCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadOptionsCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_50; uint8_t x_73; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 10);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 12);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_23 = lean_ctor_get(x_6, 13);
lean_inc_ref(x_23);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 lean_ctor_release(x_6, 12);
 lean_ctor_release(x_6, 13);
 x_24 = x_6;
} else {
 lean_dec_ref(x_6);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_25);
lean_dec(x_9);
x_26 = lean_apply_1(x_4, x_12);
x_27 = l_Lean_diagnostics;
x_28 = l_Lean_Option_get___redArg(x_1, x_26, x_27);
x_73 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_unbox(x_28);
if (x_74 == 0)
{
x_29 = x_10;
x_30 = x_11;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_7;
x_43 = lean_box(0);
goto block_49;
}
else
{
x_50 = x_73;
goto block_72;
}
}
else
{
uint8_t x_75; 
x_75 = lean_unbox(x_28);
x_50 = x_75;
goto block_72;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_2, x_26, x_44);
if (lean_is_scalar(x_24)) {
 x_46 = lean_alloc_ctor(0, 14, 2);
} else {
 x_46 = x_24;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_26);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_32);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_35);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set(x_46, 10, x_37);
lean_ctor_set(x_46, 11, x_38);
lean_ctor_set(x_46, 12, x_39);
lean_ctor_set(x_46, 13, x_41);
x_47 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*14, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*14 + 1, x_40);
x_48 = lean_apply_3(x_5, x_46, x_42, lean_box(0));
return x_48;
}
block_72:
{
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_st_ref_take(x_7);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 5);
lean_dec(x_54);
x_55 = lean_unbox(x_28);
x_56 = l_Lean_Kernel_enableDiag(x_53, x_55);
x_57 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_51, 5, x_57);
lean_ctor_set(x_51, 0, x_56);
x_58 = lean_st_ref_set(x_7, x_51);
x_29 = x_10;
x_30 = x_11;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_7;
x_43 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 2);
x_62 = lean_ctor_get(x_51, 3);
x_63 = lean_ctor_get(x_51, 4);
x_64 = lean_ctor_get(x_51, 6);
x_65 = lean_ctor_get(x_51, 7);
x_66 = lean_ctor_get(x_51, 8);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_67 = lean_unbox(x_28);
x_68 = l_Lean_Kernel_enableDiag(x_59, x_67);
x_69 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_61);
lean_ctor_set(x_70, 3, x_62);
lean_ctor_set(x_70, 4, x_63);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_64);
lean_ctor_set(x_70, 7, x_65);
lean_ctor_set(x_70, 8, x_66);
x_71 = lean_st_ref_set(x_7, x_70);
x_29 = x_10;
x_30 = x_11;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_7;
x_43 = lean_box(0);
goto block_49;
}
}
else
{
x_29 = x_10;
x_30 = x_11;
x_31 = x_13;
x_32 = x_14;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_7;
x_43 = lean_box(0);
goto block_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_instMonadWithOptionsCoreM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_KVMap_instValueNat;
x_2 = l_Lean_KVMap_instValueBool;
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadWithOptionsCoreM___lam__0___boxed), 8, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_instMonadWithOptionsCoreM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_35; uint8_t x_58; 
x_5 = l_Lean_inheritedTraceOptions;
x_6 = lean_st_ref_get(x_5);
x_7 = l_Lean_KVMap_instValueBool;
x_8 = l_Lean_KVMap_instValueNat;
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 10);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 12);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_23 = x_2;
} else {
 lean_dec_ref(x_2);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_24);
lean_dec(x_9);
x_25 = l_Lean_diagnostics;
x_26 = l_Lean_Option_get___redArg(x_7, x_12, x_25);
x_58 = l_Lean_Kernel_isDiagnosticsEnabled(x_24);
lean_dec_ref(x_24);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_unbox(x_26);
if (x_59 == 0)
{
x_27 = x_3;
x_28 = lean_box(0);
goto block_34;
}
else
{
x_35 = x_58;
goto block_57;
}
}
else
{
uint8_t x_60; 
x_60 = lean_unbox(x_26);
x_35 = x_60;
goto block_57;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___redArg(x_8, x_12, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 14, 2);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_11);
lean_ctor_set(x_31, 2, x_12);
lean_ctor_set(x_31, 3, x_13);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_14);
lean_ctor_set(x_31, 6, x_15);
lean_ctor_set(x_31, 7, x_16);
lean_ctor_set(x_31, 8, x_17);
lean_ctor_set(x_31, 9, x_18);
lean_ctor_set(x_31, 10, x_19);
lean_ctor_set(x_31, 11, x_20);
lean_ctor_set(x_31, 12, x_21);
lean_ctor_set(x_31, 13, x_6);
x_32 = lean_unbox(x_26);
lean_dec(x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_32);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_22);
x_33 = lean_apply_3(x_1, x_31, x_27, lean_box(0));
return x_33;
}
block_57:
{
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_st_ref_take(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 5);
lean_dec(x_39);
x_40 = lean_unbox(x_26);
x_41 = l_Lean_Kernel_enableDiag(x_38, x_40);
x_42 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_36, 5, x_42);
lean_ctor_set(x_36, 0, x_41);
x_43 = lean_st_ref_set(x_3, x_36);
x_27 = x_3;
x_28 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
x_46 = lean_ctor_get(x_36, 2);
x_47 = lean_ctor_get(x_36, 3);
x_48 = lean_ctor_get(x_36, 4);
x_49 = lean_ctor_get(x_36, 6);
x_50 = lean_ctor_get(x_36, 7);
x_51 = lean_ctor_get(x_36, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_52 = lean_unbox(x_26);
x_53 = l_Lean_Kernel_enableDiag(x_44, x_52);
x_54 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_49);
lean_ctor_set(x_55, 7, x_50);
lean_ctor_set(x_55, 8, x_51);
x_56 = lean_st_ref_set(x_3, x_55);
x_27 = x_3;
x_28 = lean_box(0);
goto block_34;
}
}
else
{
x_27 = x_3;
x_28 = lean_box(0);
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_49; uint8_t x_72; 
x_6 = l_Lean_inheritedTraceOptions;
x_7 = lean_st_ref_get(x_6);
x_8 = l_Lean_KVMap_instValueBool;
x_9 = l_Lean_KVMap_instValueNat;
x_10 = lean_st_ref_get(x_4);
x_11 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 11);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 12);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 x_24 = x_3;
} else {
 lean_dec_ref(x_3);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_25);
lean_dec(x_10);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_8, x_13, x_26);
x_72 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_unbox(x_27);
if (x_73 == 0)
{
x_28 = x_11;
x_29 = x_12;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_7;
x_41 = x_4;
x_42 = lean_box(0);
goto block_48;
}
else
{
x_49 = x_72;
goto block_71;
}
}
else
{
uint8_t x_74; 
x_74 = lean_unbox(x_27);
x_49 = x_74;
goto block_71;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = l_Lean_maxRecDepth;
x_44 = l_Lean_Option_get___redArg(x_9, x_13, x_43);
if (lean_is_scalar(x_24)) {
 x_45 = lean_alloc_ctor(0, 14, 2);
} else {
 x_45 = x_24;
}
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_13);
lean_ctor_set(x_45, 3, x_30);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_31);
lean_ctor_set(x_45, 6, x_32);
lean_ctor_set(x_45, 7, x_33);
lean_ctor_set(x_45, 8, x_34);
lean_ctor_set(x_45, 9, x_35);
lean_ctor_set(x_45, 10, x_36);
lean_ctor_set(x_45, 11, x_37);
lean_ctor_set(x_45, 12, x_38);
lean_ctor_set(x_45, 13, x_40);
x_46 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_45, sizeof(void*)*14, x_46);
lean_ctor_set_uint8(x_45, sizeof(void*)*14 + 1, x_39);
x_47 = lean_apply_3(x_2, x_45, x_41, lean_box(0));
return x_47;
}
block_71:
{
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_st_ref_take(x_4);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 5);
lean_dec(x_53);
x_54 = lean_unbox(x_27);
x_55 = l_Lean_Kernel_enableDiag(x_52, x_54);
x_56 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_50, 5, x_56);
lean_ctor_set(x_50, 0, x_55);
x_57 = lean_st_ref_set(x_4, x_50);
x_28 = x_11;
x_29 = x_12;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_7;
x_41 = x_4;
x_42 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
x_60 = lean_ctor_get(x_50, 2);
x_61 = lean_ctor_get(x_50, 3);
x_62 = lean_ctor_get(x_50, 4);
x_63 = lean_ctor_get(x_50, 6);
x_64 = lean_ctor_get(x_50, 7);
x_65 = lean_ctor_get(x_50, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_66 = lean_unbox(x_27);
x_67 = l_Lean_Kernel_enableDiag(x_58, x_66);
x_68 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_69 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_59);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_62);
lean_ctor_set(x_69, 5, x_68);
lean_ctor_set(x_69, 6, x_63);
lean_ctor_set(x_69, 7, x_64);
lean_ctor_set(x_69, 8, x_65);
x_70 = lean_st_ref_set(x_4, x_69);
x_28 = x_11;
x_29 = x_12;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_7;
x_41 = x_4;
x_42 = lean_box(0);
goto block_48;
}
}
else
{
x_28 = x_11;
x_29 = x_12;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_7;
x_41 = x_4;
x_42 = lean_box(0);
goto block_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Core_instMonadCoreM___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_12 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_6);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_8);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_7);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_17);
lean_ctor_set(x_3, 2, x_18);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_12);
x_19 = ((lean_object*)(l_Lean_Core_instMonadEnvCoreM));
x_20 = ((lean_object*)(l_Lean_Core_instMonadOptionsCoreM___closed__0));
x_21 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_26 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_27 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_22);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_25);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_24);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_34);
x_35 = ((lean_object*)(l_Lean_Core_instMonadEnvCoreM));
x_36 = ((lean_object*)(l_Lean_Core_instMonadOptionsCoreM___closed__0));
x_37 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_1);
lean_closure_set(x_37, 2, x_35);
lean_closure_set(x_37, 3, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_45 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_39);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_42);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_41);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_40);
if (lean_is_scalar(x_43)) {
 x_52 = lean_alloc_ctor(0, 5, 0);
} else {
 x_52 = x_43;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = ((lean_object*)(l_Lean_Core_instMonadEnvCoreM));
x_55 = ((lean_object*)(l_Lean_Core_instMonadOptionsCoreM___closed__0));
x_56 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, x_53);
lean_closure_set(x_56, 2, x_54);
lean_closure_set(x_56, 3, x_55);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 2);
lean_dec(x_7);
lean_ctor_set(x_5, 2, x_1);
x_8 = lean_st_ref_set(x_3, x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_5, 6);
x_17 = lean_ctor_get(x_5, 7);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_1);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 3);
lean_dec(x_7);
lean_ctor_set(x_5, 3, x_1);
x_8 = lean_st_ref_set(x_3, x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_5, 6);
x_17 = lean_ctor_get(x_5, 7);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_1);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadDeclNameGeneratorCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 3);
lean_dec(x_8);
lean_ctor_set(x_4, 3, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
x_18 = lean_ctor_get(x_4, 9);
x_19 = lean_ctor_get(x_4, 10);
x_20 = lean_ctor_get(x_4, 11);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
x_22 = lean_ctor_get(x_4, 12);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*14 + 1);
x_24 = lean_ctor_get(x_4, 13);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_2);
lean_ctor_set(x_25, 4, x_13);
lean_ctor_set(x_25, 5, x_14);
lean_ctor_set(x_25, 6, x_15);
lean_ctor_set(x_25, 7, x_16);
lean_ctor_set(x_25, 8, x_17);
lean_ctor_set(x_25, 9, x_18);
lean_ctor_set(x_25, 10, x_19);
lean_ctor_set(x_25, 11, x_20);
lean_ctor_set(x_25, 12, x_22);
lean_ctor_set(x_25, 13, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*14, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*14 + 1, x_23);
x_26 = lean_apply_3(x_3, x_25, x_5, lean_box(0));
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instMonadRecDepthCoreM___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_st_ref_set(x_3, x_5);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 11);
lean_dec(x_12);
lean_ctor_set(x_2, 11, x_7);
x_13 = lean_apply_3(x_1, x_2, x_3, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
x_19 = lean_ctor_get(x_2, 5);
x_20 = lean_ctor_get(x_2, 6);
x_21 = lean_ctor_get(x_2, 7);
x_22 = lean_ctor_get(x_2, 8);
x_23 = lean_ctor_get(x_2, 9);
x_24 = lean_ctor_get(x_2, 10);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_26 = lean_ctor_get(x_2, 12);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_28 = lean_ctor_get(x_2, 13);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_19);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_7);
lean_ctor_set(x_29, 12, x_26);
lean_ctor_set(x_29, 13, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*14, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*14 + 1, x_27);
x_30 = lean_apply_3(x_1, x_29, x_3, lean_box(0));
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_5, 2);
x_34 = lean_ctor_get(x_5, 3);
x_35 = lean_ctor_get(x_5, 4);
x_36 = lean_ctor_get(x_5, 5);
x_37 = lean_ctor_get(x_5, 6);
x_38 = lean_ctor_get(x_5, 7);
x_39 = lean_ctor_get(x_5, 8);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_32, x_40);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_33);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_35);
lean_ctor_set(x_42, 5, x_36);
lean_ctor_set(x_42, 6, x_37);
lean_ctor_set(x_42, 7, x_38);
lean_ctor_set(x_42, 8, x_39);
x_43 = lean_st_ref_set(x_3, x_42);
x_44 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_2, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 7);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 8);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 9);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 10);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_56 = lean_ctor_get(x_2, 12);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_58 = lean_ctor_get(x_2, 13);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_59 = x_2;
} else {
 lean_dec_ref(x_2);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 14, 2);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_45);
lean_ctor_set(x_60, 2, x_46);
lean_ctor_set(x_60, 3, x_47);
lean_ctor_set(x_60, 4, x_48);
lean_ctor_set(x_60, 5, x_49);
lean_ctor_set(x_60, 6, x_50);
lean_ctor_set(x_60, 7, x_51);
lean_ctor_set(x_60, 8, x_52);
lean_ctor_set(x_60, 9, x_53);
lean_ctor_set(x_60, 10, x_54);
lean_ctor_set(x_60, 11, x_32);
lean_ctor_set(x_60, 12, x_56);
lean_ctor_set(x_60, 13, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*14, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*14 + 1, x_57);
x_61 = lean_apply_3(x_1, x_60, x_3, lean_box(0));
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_withFreshMacroScope___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 11);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 10);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 7);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadInfoTreeCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 7);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 7, x_8);
x_9 = lean_st_ref_set(x_3, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_19);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_21);
lean_ctor_set(x_22, 8, x_20);
x_23 = lean_st_ref_set(x_3, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadInfoTreeCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = lean_apply_1(x_1, x_6);
lean_ctor_set(x_4, 5, x_7);
x_8 = lean_st_ref_set(x_2, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_20 = lean_apply_1(x_1, x_16);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set(x_21, 7, x_18);
lean_ctor_set(x_21, 8, x_19);
x_22 = lean_st_ref_set(x_2, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyCache___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 5, x_8);
x_9 = lean_st_ref_set(x_3, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_17);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
x_23 = lean_st_ref_set(x_3, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyCache(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_6, 0, x_9);
x_10 = lean_st_ref_set(x_2, x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_apply_1(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_4, 5, x_16);
x_17 = lean_st_ref_set(x_2, x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 3);
x_25 = lean_ctor_get(x_4, 4);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get(x_4, 7);
x_28 = lean_ctor_get(x_4, 8);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_20);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_29 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
x_32 = lean_apply_1(x_1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_24);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_26);
lean_ctor_set(x_34, 7, x_27);
lean_ctor_set(x_34, 8, x_28);
x_35 = lean_st_ref_set(x_2, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelTypeCache___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_7, 0, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_apply_1(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_5, 5, x_17);
x_18 = lean_st_ref_set(x_3, x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_5, 5);
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 6);
x_28 = lean_ctor_get(x_5, 7);
x_29 = lean_ctor_get(x_5, 8);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_21);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_30 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
x_33 = lean_apply_1(x_1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_27);
lean_ctor_set(x_35, 7, x_28);
lean_ctor_set(x_35, 8, x_29);
x_36 = lean_st_ref_set(x_3, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelTypeCache(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_6, 1, x_9);
x_10 = lean_st_ref_set(x_2, x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_4, 5, x_16);
x_17 = lean_st_ref_set(x_2, x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 3);
x_25 = lean_ctor_get(x_4, 4);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get(x_4, 7);
x_28 = lean_ctor_get(x_4, 8);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_20);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_29 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
x_32 = lean_apply_1(x_1, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_24);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_26);
lean_ctor_set(x_34, 7, x_27);
lean_ctor_set(x_34, 8, x_28);
x_35 = lean_st_ref_set(x_2, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelValueCache___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_7, 1, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_5, 5, x_17);
x_18 = lean_st_ref_set(x_3, x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_5, 5);
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 6);
x_28 = lean_ctor_get(x_5, 7);
x_29 = lean_ctor_get(x_5, 8);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_21);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_30 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
x_33 = lean_apply_1(x_1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_27);
lean_ctor_set(x_35, 7, x_28);
lean_ctor_set(x_35, 8, x_29);
x_36 = lean_st_ref_set(x_3, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelValueCache(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_level_eq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_50; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 5);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_50 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(x_7, x_9);
if (lean_obj_tag(x_50) == 1)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(x_2, x_53);
lean_dec(x_53);
if (x_55 == 0)
{
lean_dec(x_54);
lean_free_object(x_50);
x_10 = x_3;
x_11 = lean_box(0);
goto block_49;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(x_2, x_57);
lean_dec(x_57);
if (x_59 == 0)
{
lean_dec(x_58);
x_10 = x_3;
x_11 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
}
else
{
lean_dec(x_50);
x_10 = x_3;
x_11 = lean_box(0);
goto block_49;
}
block_49:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_take(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_2);
x_17 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_17);
if (lean_is_scalar(x_8)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_8;
}
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_16, x_9, x_18);
lean_ctor_set(x_14, 0, x_19);
x_20 = lean_st_ref_set(x_10, x_12);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
lean_inc(x_2);
x_24 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_24);
if (lean_is_scalar(x_8)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_8;
}
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_22, x_9, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_12, 5, x_27);
x_28 = lean_st_ref_set(x_10, x_12);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_12, 5);
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
x_33 = lean_ctor_get(x_12, 2);
x_34 = lean_ctor_get(x_12, 3);
x_35 = lean_ctor_get(x_12, 4);
x_36 = lean_ctor_get(x_12, 6);
x_37 = lean_ctor_get(x_12, 7);
x_38 = lean_ctor_get(x_12, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_30);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_39 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
lean_inc(x_2);
x_42 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
lean_inc_ref(x_42);
if (lean_is_scalar(x_8)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_8;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_39, x_9, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_46, 2, x_33);
lean_ctor_set(x_46, 3, x_34);
lean_ctor_set(x_46, 4, x_35);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_46, 6, x_36);
lean_ctor_set(x_46, 7, x_37);
lean_ctor_set(x_46, 8, x_38);
x_47 = lean_st_ref_set(x_10, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_42);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instantiateValueLevelParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_instantiateValueLevelParams___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_st_ref_get(x_4);
x_64 = lean_ctor_get(x_63, 5);
lean_inc_ref(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_ConstantInfo_name(x_1);
x_67 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1___redArg(x_65, x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 1)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(x_2, x_70);
lean_dec(x_70);
if (x_72 == 0)
{
lean_dec(x_71);
lean_free_object(x_67);
x_49 = x_3;
x_50 = x_4;
x_51 = lean_box(0);
goto block_62;
}
else
{
lean_dec(x_2);
lean_ctor_set_tag(x_67, 0);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_List_beq___at___00Lean_Core_instantiateTypeLevelParams_spec__2(x_2, x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_dec(x_75);
x_49 = x_3;
x_50 = x_4;
x_51 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_77; 
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
lean_dec(x_67);
x_49 = x_3;
x_50 = x_4;
x_51 = lean_box(0);
goto block_62;
}
block_48:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_2);
x_13 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_14 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_12, x_14, x_15);
lean_ctor_set(x_10, 1, x_16);
x_17 = lean_st_ref_set(x_6, x_8);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_2);
x_21 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_22 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_20, x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_8, 5, x_25);
x_26 = lean_st_ref_set(x_6, x_8);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
x_31 = lean_ctor_get(x_8, 2);
x_32 = lean_ctor_get(x_8, 3);
x_33 = lean_ctor_get(x_8, 4);
x_34 = lean_ctor_get(x_8, 6);
x_35 = lean_ctor_get(x_8, 7);
x_36 = lean_ctor_get(x_8, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_28);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_37 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_39 = x_28;
} else {
 lean_dec_ref(x_28);
 x_39 = lean_box(0);
}
lean_inc(x_2);
x_40 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_41 = l_Lean_ConstantInfo_name(x_1);
lean_inc_ref(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0___redArg(x_38, x_41, x_42);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_30);
lean_ctor_set(x_45, 2, x_31);
lean_ctor_set(x_45, 3, x_32);
lean_ctor_set(x_45, 4, x_33);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_34);
lean_ctor_set(x_45, 7, x_35);
lean_ctor_set(x_45, 8, x_36);
x_46 = lean_st_ref_set(x_6, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_40);
return x_47;
}
}
block_62:
{
uint8_t x_52; uint8_t x_53; 
x_52 = 0;
x_53 = l_Lean_ConstantInfo_hasValue(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_2);
x_54 = l_Lean_Core_instantiateValueLevelParams___closed__1;
x_55 = l_Lean_ConstantInfo_name(x_1);
x_56 = l_Lean_MessageData_ofConstName(x_55, x_52);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_57, x_49, x_50);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
x_6 = x_50;
x_7 = lean_box(0);
goto block_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_io_error_to_string(x_9);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_io_error_to_string(x_15);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_liftIOCore___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_3, 5);
x_13 = lean_io_error_to_string(x_11);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_io_error_to_string(x_17);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_liftIOCore(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 4, x_8);
x_9 = lean_st_ref_set(x_3, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_16);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
x_23 = lean_st_ref_set(x_3, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadTraceCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 13);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_saveState___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_6; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
x_11 = lean_st_ref_set(x_4, x_9);
lean_dec(x_4);
x_12 = l_IO_addHeartbeats(x_10);
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_17 = lean_st_ref_set(x_4, x_15);
lean_dec(x_4);
x_18 = l_IO_addHeartbeats(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_io_get_num_heartbeats();
lean_inc(x_4);
x_21 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_25 = lean_io_get_num_heartbeats();
x_26 = lean_nat_sub(x_25, x_20);
lean_dec(x_20);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_31 = lean_io_get_num_heartbeats();
x_32 = lean_nat_sub(x_31, x_20);
lean_dec(x_20);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withRestoreOrSaveFull___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withRestoreOrSaveFull___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withRestoreOrSaveFull(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 6);
x_9 = lean_ctor_get(x_6, 7);
x_10 = lean_ctor_get(x_6, 8);
x_11 = lean_ctor_get(x_4, 8);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 7);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_ctor_set(x_4, 8, x_10);
lean_ctor_set(x_4, 7, x_9);
lean_ctor_set(x_4, 6, x_8);
lean_ctor_set(x_4, 0, x_7);
x_15 = lean_st_ref_set(x_2, x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 6);
x_21 = lean_ctor_get(x_18, 7);
x_22 = lean_ctor_get(x_18, 8);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
lean_inc_ref(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_19);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_20);
lean_ctor_set(x_28, 7, x_21);
lean_ctor_set(x_28, 8, x_22);
x_29 = lean_st_ref_set(x_2, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_SavedState_restore___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 10);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 11);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_addMacroScope(x_5, x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Core_withFreshMacroScope___redArg(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_mkFreshUserName(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_47; uint8_t x_70; 
x_5 = lean_st_mk_ref(x_3);
x_6 = l_Lean_inheritedTraceOptions;
x_7 = lean_st_ref_get(x_6);
x_8 = l_Lean_KVMap_instValueBool;
x_9 = l_Lean_KVMap_instValueNat;
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 11);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 12);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_25);
lean_dec(x_10);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_8, x_13, x_26);
x_70 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = lean_unbox(x_27);
if (x_71 == 0)
{
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_46;
}
else
{
x_47 = x_70;
goto block_69;
}
}
else
{
uint8_t x_72; 
x_72 = lean_unbox(x_27);
x_47 = x_72;
goto block_69;
}
block_46:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = l_Lean_maxRecDepth;
x_31 = l_Lean_Option_get___redArg(x_9, x_13, x_30);
if (lean_is_scalar(x_24)) {
 x_32 = lean_alloc_ctor(0, 14, 2);
} else {
 x_32 = x_24;
}
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_32, 2, x_13);
lean_ctor_set(x_32, 3, x_14);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_15);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_22);
lean_ctor_set(x_32, 13, x_7);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_23);
x_34 = lean_apply_3(x_1, x_32, x_28, lean_box(0));
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_st_ref_get(x_5);
lean_dec(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_st_ref_get(x_5);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
block_69:
{
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_st_ref_take(x_5);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 5);
lean_dec(x_51);
x_52 = lean_unbox(x_27);
x_53 = l_Lean_Kernel_enableDiag(x_50, x_52);
x_54 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_48, 5, x_54);
lean_ctor_set(x_48, 0, x_53);
x_55 = lean_st_ref_set(x_5, x_48);
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
x_58 = lean_ctor_get(x_48, 2);
x_59 = lean_ctor_get(x_48, 3);
x_60 = lean_ctor_get(x_48, 4);
x_61 = lean_ctor_get(x_48, 6);
x_62 = lean_ctor_get(x_48, 7);
x_63 = lean_ctor_get(x_48, 8);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_64 = lean_unbox(x_27);
x_65 = l_Lean_Kernel_enableDiag(x_56, x_64);
x_66 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_57);
lean_ctor_set(x_67, 2, x_58);
lean_ctor_set(x_67, 3, x_59);
lean_ctor_set(x_67, 4, x_60);
lean_ctor_set(x_67, 5, x_66);
lean_ctor_set(x_67, 6, x_61);
lean_ctor_set(x_67, 7, x_62);
lean_ctor_set(x_67, 8, x_63);
x_68 = lean_st_ref_set(x_5, x_67);
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_46;
}
}
else
{
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_61; uint8_t x_84; 
x_6 = lean_st_mk_ref(x_4);
x_7 = l_Lean_inheritedTraceOptions;
x_8 = lean_st_ref_get(x_7);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 12);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_26);
lean_dec(x_11);
x_27 = l_Lean_diagnostics;
x_28 = l_Lean_Option_get___redArg(x_9, x_14, x_27);
x_84 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec_ref(x_26);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = lean_unbox(x_28);
if (x_85 == 0)
{
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_60;
}
else
{
x_61 = x_84;
goto block_83;
}
}
else
{
uint8_t x_86; 
x_86 = lean_unbox(x_28);
x_61 = x_86;
goto block_83;
}
block_60:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_10, x_14, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 14, 2);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_14);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_32);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_35);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set(x_46, 10, x_37);
lean_ctor_set(x_46, 11, x_38);
lean_ctor_set(x_46, 12, x_39);
lean_ctor_set(x_46, 13, x_41);
x_47 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*14, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*14 + 1, x_40);
x_48 = lean_apply_3(x_2, x_46, x_42, lean_box(0));
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_st_ref_get(x_6);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_st_ref_get(x_6);
lean_dec(x_6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
block_83:
{
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_st_ref_take(x_6);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 5);
lean_dec(x_65);
x_66 = lean_unbox(x_28);
x_67 = l_Lean_Kernel_enableDiag(x_64, x_66);
x_68 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_62, 5, x_68);
lean_ctor_set(x_62, 0, x_67);
x_69 = lean_st_ref_set(x_6, x_62);
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
x_72 = lean_ctor_get(x_62, 2);
x_73 = lean_ctor_get(x_62, 3);
x_74 = lean_ctor_get(x_62, 4);
x_75 = lean_ctor_get(x_62, 6);
x_76 = lean_ctor_get(x_62, 7);
x_77 = lean_ctor_get(x_62, 8);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_78 = lean_unbox(x_28);
x_79 = l_Lean_Kernel_enableDiag(x_70, x_78);
x_80 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_81 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_71);
lean_ctor_set(x_81, 2, x_72);
lean_ctor_set(x_81, 3, x_73);
lean_ctor_set(x_81, 4, x_74);
lean_ctor_set(x_81, 5, x_80);
lean_ctor_set(x_81, 6, x_75);
lean_ctor_set(x_81, 7, x_76);
lean_ctor_set(x_81, 8, x_77);
x_82 = lean_st_ref_set(x_6, x_81);
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_60;
}
}
else
{
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_41; uint8_t x_64; 
x_5 = lean_st_mk_ref(x_3);
x_6 = l_Lean_inheritedTraceOptions;
x_7 = lean_st_ref_get(x_6);
x_8 = l_Lean_KVMap_instValueBool;
x_9 = l_Lean_KVMap_instValueNat;
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 11);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 12);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_25);
lean_dec(x_10);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_8, x_13, x_26);
x_64 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = lean_unbox(x_27);
if (x_65 == 0)
{
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_40;
}
else
{
x_41 = x_64;
goto block_63;
}
}
else
{
uint8_t x_66; 
x_66 = lean_unbox(x_27);
x_41 = x_66;
goto block_63;
}
block_40:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = l_Lean_maxRecDepth;
x_31 = l_Lean_Option_get___redArg(x_9, x_13, x_30);
if (lean_is_scalar(x_24)) {
 x_32 = lean_alloc_ctor(0, 14, 2);
} else {
 x_32 = x_24;
}
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_32, 2, x_13);
lean_ctor_set(x_32, 3, x_14);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_15);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_22);
lean_ctor_set(x_32, 13, x_7);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_23);
x_34 = lean_apply_3(x_1, x_32, x_28, lean_box(0));
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_st_ref_get(x_5);
lean_dec(x_5);
lean_dec(x_36);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_st_ref_get(x_5);
lean_dec(x_5);
lean_dec(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
}
else
{
lean_dec(x_5);
return x_34;
}
}
block_63:
{
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_take(x_5);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 5);
lean_dec(x_45);
x_46 = lean_unbox(x_27);
x_47 = l_Lean_Kernel_enableDiag(x_44, x_46);
x_48 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_42, 5, x_48);
lean_ctor_set(x_42, 0, x_47);
x_49 = lean_st_ref_set(x_5, x_42);
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
x_52 = lean_ctor_get(x_42, 2);
x_53 = lean_ctor_get(x_42, 3);
x_54 = lean_ctor_get(x_42, 4);
x_55 = lean_ctor_get(x_42, 6);
x_56 = lean_ctor_get(x_42, 7);
x_57 = lean_ctor_get(x_42, 8);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_58 = lean_unbox(x_27);
x_59 = l_Lean_Kernel_enableDiag(x_50, x_58);
x_60 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_60);
lean_ctor_set(x_61, 6, x_55);
lean_ctor_set(x_61, 7, x_56);
lean_ctor_set(x_61, 8, x_57);
x_62 = lean_st_ref_set(x_5, x_61);
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_40;
}
}
else
{
lean_inc(x_5);
x_28 = x_5;
x_29 = lean_box(0);
goto block_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_run_x27___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_55; uint8_t x_78; 
x_6 = lean_st_mk_ref(x_4);
x_7 = l_Lean_inheritedTraceOptions;
x_8 = lean_st_ref_get(x_7);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 12);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_26);
lean_dec(x_11);
x_27 = l_Lean_diagnostics;
x_28 = l_Lean_Option_get___redArg(x_9, x_14, x_27);
x_78 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec_ref(x_26);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = lean_unbox(x_28);
if (x_79 == 0)
{
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_54;
}
else
{
x_55 = x_78;
goto block_77;
}
}
else
{
uint8_t x_80; 
x_80 = lean_unbox(x_28);
x_55 = x_80;
goto block_77;
}
block_54:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_10, x_14, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 14, 2);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_14);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_32);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_35);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set(x_46, 10, x_37);
lean_ctor_set(x_46, 11, x_38);
lean_ctor_set(x_46, 12, x_39);
lean_ctor_set(x_46, 13, x_41);
x_47 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*14, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*14 + 1, x_40);
x_48 = lean_apply_3(x_2, x_46, x_42, lean_box(0));
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_50);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
else
{
lean_dec(x_6);
return x_48;
}
}
block_77:
{
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_st_ref_take(x_6);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 5);
lean_dec(x_59);
x_60 = lean_unbox(x_28);
x_61 = l_Lean_Kernel_enableDiag(x_58, x_60);
x_62 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_56, 5, x_62);
lean_ctor_set(x_56, 0, x_61);
x_63 = lean_st_ref_set(x_6, x_56);
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
x_66 = lean_ctor_get(x_56, 2);
x_67 = lean_ctor_get(x_56, 3);
x_68 = lean_ctor_get(x_56, 4);
x_69 = lean_ctor_get(x_56, 6);
x_70 = lean_ctor_get(x_56, 7);
x_71 = lean_ctor_get(x_56, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_72 = lean_unbox(x_28);
x_73 = l_Lean_Kernel_enableDiag(x_64, x_72);
x_74 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_75 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_65);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_74);
lean_ctor_set(x_75, 6, x_69);
lean_ctor_set(x_75, 7, x_70);
lean_ctor_set(x_75, 8, x_71);
x_76 = lean_st_ref_set(x_6, x_75);
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_54;
}
}
else
{
lean_inc(x_6);
x_29 = x_12;
x_30 = x_13;
x_31 = x_15;
x_32 = x_16;
x_33 = x_17;
x_34 = x_18;
x_35 = x_19;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_8;
x_42 = x_6;
x_43 = lean_box(0);
goto block_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_run_x27(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_65; uint8_t x_88; 
x_5 = lean_io_get_num_heartbeats();
x_6 = lean_st_mk_ref(x_3);
x_7 = l_Lean_inheritedTraceOptions;
x_8 = lean_st_ref_get(x_7);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 11);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 12);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_25);
lean_dec(x_11);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_9, x_14, x_26);
x_88 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_unbox(x_27);
if (x_89 == 0)
{
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_64;
}
else
{
x_65 = x_88;
goto block_87;
}
}
else
{
uint8_t x_90; 
x_90 = lean_unbox(x_27);
x_65 = x_90;
goto block_87;
}
block_64:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = l_Lean_maxRecDepth;
x_31 = l_Lean_Option_get___redArg(x_10, x_14, x_30);
if (lean_is_scalar(x_24)) {
 x_32 = lean_alloc_ctor(0, 14, 2);
} else {
 x_32 = x_24;
}
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_14);
lean_ctor_set(x_32, 3, x_15);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_16);
lean_ctor_set(x_32, 6, x_17);
lean_ctor_set(x_32, 7, x_18);
lean_ctor_set(x_32, 8, x_5);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_22);
lean_ctor_set(x_32, 13, x_8);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_23);
x_34 = lean_apply_3(x_1, x_32, x_28, lean_box(0));
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_st_ref_get(x_6);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_st_ref_get(x_6);
lean_dec(x_6);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_MessageData_toString(x_45);
x_47 = lean_mk_io_user_error(x_46);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec_ref(x_44);
x_49 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_50 = l_Nat_reprFast(x_48);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = lean_mk_io_user_error(x_51);
lean_ctor_set(x_34, 0, x_52);
return x_34;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_MessageData_toString(x_54);
x_56 = lean_mk_io_user_error(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec_ref(x_53);
x_59 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_60 = l_Nat_reprFast(x_58);
x_61 = lean_string_append(x_59, x_60);
lean_dec_ref(x_60);
x_62 = lean_mk_io_user_error(x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
block_87:
{
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_st_ref_take(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 5);
lean_dec(x_69);
x_70 = lean_unbox(x_27);
x_71 = l_Lean_Kernel_enableDiag(x_68, x_70);
x_72 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_66, 5, x_72);
lean_ctor_set(x_66, 0, x_71);
x_73 = lean_st_ref_set(x_6, x_66);
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
x_76 = lean_ctor_get(x_66, 2);
x_77 = lean_ctor_get(x_66, 3);
x_78 = lean_ctor_get(x_66, 4);
x_79 = lean_ctor_get(x_66, 6);
x_80 = lean_ctor_get(x_66, 7);
x_81 = lean_ctor_get(x_66, 8);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_82 = lean_unbox(x_27);
x_83 = l_Lean_Kernel_enableDiag(x_74, x_82);
x_84 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_85 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_76);
lean_ctor_set(x_85, 3, x_77);
lean_ctor_set(x_85, 4, x_78);
lean_ctor_set(x_85, 5, x_84);
lean_ctor_set(x_85, 6, x_79);
lean_ctor_set(x_85, 7, x_80);
lean_ctor_set(x_85, 8, x_81);
x_86 = lean_st_ref_set(x_6, x_85);
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_64;
}
}
else
{
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_toIO___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_79; uint8_t x_102; 
x_6 = lean_io_get_num_heartbeats();
x_7 = lean_st_mk_ref(x_4);
x_8 = l_Lean_inheritedTraceOptions;
x_9 = lean_st_ref_get(x_8);
x_10 = l_Lean_KVMap_instValueBool;
x_11 = l_Lean_KVMap_instValueNat;
x_12 = lean_st_ref_get(x_7);
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 12);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_26);
lean_dec(x_12);
x_27 = l_Lean_diagnostics;
x_28 = l_Lean_Option_get___redArg(x_10, x_15, x_27);
x_102 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec_ref(x_26);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = lean_unbox(x_28);
if (x_103 == 0)
{
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_78;
}
else
{
x_79 = x_102;
goto block_101;
}
}
else
{
uint8_t x_104; 
x_104 = lean_unbox(x_28);
x_79 = x_104;
goto block_101;
}
block_78:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_11, x_15, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 14, 2);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_15);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_32);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_35);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set(x_46, 10, x_37);
lean_ctor_set(x_46, 11, x_38);
lean_ctor_set(x_46, 12, x_39);
lean_ctor_set(x_46, 13, x_41);
x_47 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*14, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*14 + 1, x_40);
x_48 = lean_apply_3(x_2, x_46, x_42, lean_box(0));
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_st_ref_get(x_7);
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_st_ref_get(x_7);
lean_dec(x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_MessageData_toString(x_59);
x_61 = lean_mk_io_user_error(x_60);
lean_ctor_set(x_48, 0, x_61);
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec_ref(x_58);
x_63 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_64 = l_Nat_reprFast(x_62);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = lean_mk_io_user_error(x_65);
lean_ctor_set(x_48, 0, x_66);
return x_48;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
lean_dec(x_48);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_MessageData_toString(x_68);
x_70 = lean_mk_io_user_error(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec_ref(x_67);
x_73 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_74 = l_Nat_reprFast(x_72);
x_75 = lean_string_append(x_73, x_74);
lean_dec_ref(x_74);
x_76 = lean_mk_io_user_error(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
block_101:
{
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_st_ref_take(x_7);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 5);
lean_dec(x_83);
x_84 = lean_unbox(x_28);
x_85 = l_Lean_Kernel_enableDiag(x_82, x_84);
x_86 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_80, 5, x_86);
lean_ctor_set(x_80, 0, x_85);
x_87 = lean_st_ref_set(x_7, x_80);
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_88 = lean_ctor_get(x_80, 0);
x_89 = lean_ctor_get(x_80, 1);
x_90 = lean_ctor_get(x_80, 2);
x_91 = lean_ctor_get(x_80, 3);
x_92 = lean_ctor_get(x_80, 4);
x_93 = lean_ctor_get(x_80, 6);
x_94 = lean_ctor_get(x_80, 7);
x_95 = lean_ctor_get(x_80, 8);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_80);
x_96 = lean_unbox(x_28);
x_97 = l_Lean_Kernel_enableDiag(x_88, x_96);
x_98 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_99 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_89);
lean_ctor_set(x_99, 2, x_90);
lean_ctor_set(x_99, 3, x_91);
lean_ctor_set(x_99, 4, x_92);
lean_ctor_set(x_99, 5, x_98);
lean_ctor_set(x_99, 6, x_93);
lean_ctor_set(x_99, 7, x_94);
lean_ctor_set(x_99, 8, x_95);
x_100 = lean_st_ref_set(x_7, x_99);
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_78;
}
}
else
{
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_toIO(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_62; uint8_t x_85; 
x_5 = lean_io_get_num_heartbeats();
x_6 = lean_st_mk_ref(x_3);
x_7 = l_Lean_inheritedTraceOptions;
x_8 = lean_st_ref_get(x_7);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 11);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 12);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 lean_ctor_release(x_2, 10);
 lean_ctor_release(x_2, 11);
 lean_ctor_release(x_2, 12);
 lean_ctor_release(x_2, 13);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_25);
lean_dec(x_11);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_9, x_14, x_26);
x_85 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec_ref(x_25);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = lean_unbox(x_27);
if (x_86 == 0)
{
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_61;
}
else
{
x_62 = x_85;
goto block_84;
}
}
else
{
uint8_t x_87; 
x_87 = lean_unbox(x_27);
x_62 = x_87;
goto block_84;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = l_Lean_maxRecDepth;
x_31 = l_Lean_Option_get___redArg(x_10, x_14, x_30);
if (lean_is_scalar(x_24)) {
 x_32 = lean_alloc_ctor(0, 14, 2);
} else {
 x_32 = x_24;
}
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_14);
lean_ctor_set(x_32, 3, x_15);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_16);
lean_ctor_set(x_32, 6, x_17);
lean_ctor_set(x_32, 7, x_18);
lean_ctor_set(x_32, 8, x_5);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_22);
lean_ctor_set(x_32, 13, x_8);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_23);
x_34 = lean_apply_3(x_1, x_32, x_28, lean_box(0));
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_36);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_MessageData_toString(x_42);
x_44 = lean_mk_io_user_error(x_43);
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec_ref(x_41);
x_46 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_47 = l_Nat_reprFast(x_45);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = lean_mk_io_user_error(x_48);
lean_ctor_set(x_34, 0, x_49);
return x_34;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
lean_dec(x_34);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_MessageData_toString(x_51);
x_53 = lean_mk_io_user_error(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec_ref(x_50);
x_56 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_57 = l_Nat_reprFast(x_55);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
x_59 = lean_mk_io_user_error(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
block_84:
{
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_st_ref_take(x_6);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 5);
lean_dec(x_66);
x_67 = lean_unbox(x_27);
x_68 = l_Lean_Kernel_enableDiag(x_65, x_67);
x_69 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_63, 5, x_69);
lean_ctor_set(x_63, 0, x_68);
x_70 = lean_st_ref_set(x_6, x_63);
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
x_73 = lean_ctor_get(x_63, 2);
x_74 = lean_ctor_get(x_63, 3);
x_75 = lean_ctor_get(x_63, 4);
x_76 = lean_ctor_get(x_63, 6);
x_77 = lean_ctor_get(x_63, 7);
x_78 = lean_ctor_get(x_63, 8);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_79 = lean_unbox(x_27);
x_80 = l_Lean_Kernel_enableDiag(x_71, x_79);
x_81 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_82 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_72);
lean_ctor_set(x_82, 2, x_73);
lean_ctor_set(x_82, 3, x_74);
lean_ctor_set(x_82, 4, x_75);
lean_ctor_set(x_82, 5, x_81);
lean_ctor_set(x_82, 6, x_76);
lean_ctor_set(x_82, 7, x_77);
lean_ctor_set(x_82, 8, x_78);
x_83 = lean_st_ref_set(x_6, x_82);
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_61;
}
}
else
{
lean_inc(x_6);
x_28 = x_6;
x_29 = lean_box(0);
goto block_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_toIO_x27___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_76; uint8_t x_99; 
x_6 = lean_io_get_num_heartbeats();
x_7 = lean_st_mk_ref(x_4);
x_8 = l_Lean_inheritedTraceOptions;
x_9 = lean_st_ref_get(x_8);
x_10 = l_Lean_KVMap_instValueBool;
x_11 = l_Lean_KVMap_instValueNat;
x_12 = lean_st_ref_get(x_7);
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 11);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 12);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 lean_ctor_release(x_3, 11);
 lean_ctor_release(x_3, 12);
 lean_ctor_release(x_3, 13);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_26);
lean_dec(x_12);
x_27 = l_Lean_diagnostics;
x_28 = l_Lean_Option_get___redArg(x_10, x_15, x_27);
x_99 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec_ref(x_26);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_unbox(x_28);
if (x_100 == 0)
{
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_75;
}
else
{
x_76 = x_99;
goto block_98;
}
}
else
{
uint8_t x_101; 
x_101 = lean_unbox(x_28);
x_76 = x_101;
goto block_98;
}
block_75:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_11, x_15, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 14, 2);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_15);
lean_ctor_set(x_46, 3, x_31);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_32);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_35);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set(x_46, 10, x_37);
lean_ctor_set(x_46, 11, x_38);
lean_ctor_set(x_46, 12, x_39);
lean_ctor_set(x_46, 13, x_41);
x_47 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_46, sizeof(void*)*14, x_47);
lean_ctor_set_uint8(x_46, sizeof(void*)*14 + 1, x_40);
x_48 = lean_apply_3(x_2, x_46, x_42, lean_box(0));
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_dec(x_50);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_dec(x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_MessageData_toString(x_56);
x_58 = lean_mk_io_user_error(x_57);
lean_ctor_set(x_48, 0, x_58);
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec_ref(x_55);
x_60 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_61 = l_Nat_reprFast(x_59);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = lean_mk_io_user_error(x_62);
lean_ctor_set(x_48, 0, x_63);
return x_48;
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
lean_dec(x_48);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_MessageData_toString(x_65);
x_67 = lean_mk_io_user_error(x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec_ref(x_64);
x_70 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_71 = l_Nat_reprFast(x_69);
x_72 = lean_string_append(x_70, x_71);
lean_dec_ref(x_71);
x_73 = lean_mk_io_user_error(x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
block_98:
{
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_st_ref_take(x_7);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 5);
lean_dec(x_80);
x_81 = lean_unbox(x_28);
x_82 = l_Lean_Kernel_enableDiag(x_79, x_81);
x_83 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_77, 5, x_83);
lean_ctor_set(x_77, 0, x_82);
x_84 = lean_st_ref_set(x_7, x_77);
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_77, 0);
x_86 = lean_ctor_get(x_77, 1);
x_87 = lean_ctor_get(x_77, 2);
x_88 = lean_ctor_get(x_77, 3);
x_89 = lean_ctor_get(x_77, 4);
x_90 = lean_ctor_get(x_77, 6);
x_91 = lean_ctor_get(x_77, 7);
x_92 = lean_ctor_get(x_77, 8);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_77);
x_93 = lean_unbox(x_28);
x_94 = l_Lean_Kernel_enableDiag(x_85, x_93);
x_95 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_96 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_86);
lean_ctor_set(x_96, 2, x_87);
lean_ctor_set(x_96, 3, x_88);
lean_ctor_set(x_96, 4, x_89);
lean_ctor_set(x_96, 5, x_95);
lean_ctor_set(x_96, 6, x_90);
lean_ctor_set(x_96, 7, x_91);
lean_ctor_set(x_96, 8, x_92);
x_97 = lean_st_ref_set(x_7, x_96);
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_75;
}
}
else
{
lean_inc(x_7);
x_29 = x_13;
x_30 = x_14;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_6;
x_36 = x_20;
x_37 = x_21;
x_38 = x_22;
x_39 = x_23;
x_40 = x_24;
x_41 = x_9;
x_42 = x_7;
x_43 = lean_box(0);
goto block_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_toIO_x27(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
x_12 = lean_ctor_get(x_4, 5);
x_13 = lean_ctor_get(x_4, 6);
x_14 = lean_ctor_get(x_4, 7);
x_15 = lean_ctor_get(x_4, 8);
x_16 = lean_ctor_get(x_4, 9);
x_17 = lean_ctor_get(x_4, 10);
x_18 = lean_ctor_get(x_4, 11);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*14 + 1);
x_22 = lean_ctor_get(x_4, 13);
x_23 = lean_nat_dec_eq(x_10, x_11);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc_ref(x_22);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_4, 13);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 12);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 11);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 10);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 9);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 8);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 7);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 6);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 5);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 4);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_4, 0);
lean_dec(x_38);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_10, x_39);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_40);
x_41 = lean_apply_5(x_3, lean_box(0), x_1, x_4, x_5, lean_box(0));
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_10, x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_44, 2, x_9);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_11);
lean_ctor_set(x_44, 5, x_12);
lean_ctor_set(x_44, 6, x_13);
lean_ctor_set(x_44, 7, x_14);
lean_ctor_set(x_44, 8, x_15);
lean_ctor_set(x_44, 9, x_16);
lean_ctor_set(x_44, 10, x_17);
lean_ctor_set(x_44, 11, x_18);
lean_ctor_set(x_44, 12, x_20);
lean_ctor_set(x_44, 13, x_22);
lean_ctor_set_uint8(x_44, sizeof(void*)*14, x_19);
lean_ctor_set_uint8(x_44, sizeof(void*)*14 + 1, x_21);
x_45 = lean_apply_5(x_3, lean_box(0), x_1, x_44, x_5, lean_box(0));
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_3);
lean_dec(x_1);
lean_inc(x_12);
x_46 = l_Lean_throwMaxRecDepthAt___redArg(x_2, x_12);
x_47 = lean_apply_3(x_46, x_4, x_5, lean_box(0));
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withIncRecDepth___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadExceptOfEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__2;
x_2 = l_Lean_Core_withIncRecDepth___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_withIncRecDepth___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_withIncRecDepth___redArg___closed__5;
x_2 = l_Lean_Core_withIncRecDepth___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Core_instMonadCoreM___closed__1;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_15 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_9);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_21, 0, x_10);
lean_ctor_set(x_6, 4, x_19);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 2, x_21);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_15);
x_22 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_23 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_24 = l_Lean_Core_instAddMessageContextCoreM;
x_25 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_24, x_4);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec_ref(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_26);
x_31 = lean_apply_2(x_28, lean_box(0), x_30);
x_32 = lean_apply_1(x_29, lean_box(0));
x_33 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_31, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 2);
x_36 = lean_ctor_get(x_6, 3);
x_37 = lean_ctor_get(x_6, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_38 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_39 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_34);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_37);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_35);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_43);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_46);
x_47 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_48 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_49 = l_Lean_Core_instAddMessageContextCoreM;
x_50 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_49, x_4);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec_ref(x_2);
x_55 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_55, 0, x_3);
lean_closure_set(x_55, 1, x_51);
x_56 = lean_apply_2(x_53, lean_box(0), x_55);
x_57 = lean_apply_1(x_54, lean_box(0));
x_58 = lean_apply_4(x_52, lean_box(0), lean_box(0), x_56, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_66 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_60);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_67, 0, x_60);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_60);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_70, 0, x_63);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_71, 0, x_62);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_72, 0, x_61);
if (lean_is_scalar(x_64)) {
 x_73 = lean_alloc_ctor(0, 5, 0);
} else {
 x_73 = x_64;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_75 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_76 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_77 = l_Lean_Core_instAddMessageContextCoreM;
x_78 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_77, x_74);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec_ref(x_2);
x_83 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_83, 0, x_3);
lean_closure_set(x_83, 1, x_79);
x_84 = lean_apply_2(x_81, lean_box(0), x_83);
x_85 = lean_apply_1(x_82, lean_box(0));
x_86 = lean_apply_4(x_80, lean_box(0), lean_box(0), x_84, x_85);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withIncRecDepth___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Core_instMonadCoreM___closed__1;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_15 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_9);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_21, 0, x_10);
lean_ctor_set(x_6, 4, x_19);
lean_ctor_set(x_6, 3, x_20);
lean_ctor_set(x_6, 2, x_21);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_15);
x_22 = lean_ctor_get(x_1, 12);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 1)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_IO_CancelToken_isSet(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = lean_box(0);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_22);
x_27 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_28 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_29 = l_Lean_Core_instAddMessageContextCoreM;
x_30 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_29, x_4);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_Lean_throwInterruptException___redArg(x_31);
x_33 = lean_apply_3(x_32, x_1, x_2, lean_box(0));
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = l_IO_CancelToken_isSet(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_39 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_40 = l_Lean_Core_instAddMessageContextCoreM;
x_41 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_40, x_4);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_throwInterruptException___redArg(x_42);
x_44 = lean_apply_3(x_43, x_1, x_2, lean_box(0));
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_22);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_6, 0);
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_ctor_get(x_6, 3);
x_50 = lean_ctor_get(x_6, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_6);
x_51 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_52 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_47);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_53, 0, x_47);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_49);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_58, 0, x_48);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_4, 1, x_52);
lean_ctor_set(x_4, 0, x_59);
x_60 = lean_ctor_get(x_1, 12);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = l_IO_CancelToken_isSet(x_61);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_64 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_62;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
x_66 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_67 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_68 = l_Lean_Core_instAddMessageContextCoreM;
x_69 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_68, x_4);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_69);
x_71 = l_Lean_throwInterruptException___redArg(x_70);
x_72 = lean_apply_3(x_71, x_1, x_2, lean_box(0));
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_75 = lean_ctor_get(x_4, 0);
lean_inc(x_75);
lean_dec(x_4);
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
x_81 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__2));
x_82 = ((lean_object*)(l_Lean_Core_instMonadCoreM___closed__3));
lean_inc_ref(x_76);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_83, 0, x_76);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_84, 0, x_76);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_86, 0, x_79);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_87, 0, x_78);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_88, 0, x_77);
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_87);
lean_ctor_set(x_89, 4, x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
x_91 = lean_ctor_get(x_1, 12);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 1)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = l_IO_CancelToken_isSet(x_92);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_90);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 1, 0);
} else {
 x_96 = x_93;
 lean_ctor_set_tag(x_96, 0);
}
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
x_97 = l_Lean_Core_withIncRecDepth___redArg___closed__6;
x_98 = ((lean_object*)(l_Lean_Core_instMonadRefCoreM));
x_99 = l_Lean_Core_instAddMessageContextCoreM;
x_100 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_99, x_90);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_100);
x_102 = l_Lean_throwInterruptException___redArg(x_101);
x_103 = lean_apply_3(x_102, x_1, x_2, lean_box(0));
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_2);
lean_dec_ref(x_1);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_checkInterrupted(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_));
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_));
x_3 = l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_Core_initFn___closed__5_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_36; uint8_t x_37; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 5);
x_36 = l_Lean_Core_debug_moduleNameAtTimeout;
x_37 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_6, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_8 = x_38;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__12));
x_40 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_37);
x_41 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__13));
x_43 = lean_string_append(x_41, x_42);
x_8 = x_43;
goto block_35;
}
block_35:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__1));
x_10 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__3;
x_11 = l_Lean_stringToMessageData(x_8);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(1000u);
x_16 = lean_nat_div(x_3, x_15);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__7;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__9;
x_24 = l_Lean_MessageData_ofName(x_2);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Core_throwMaxHeartbeat___redArg___closed__11;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_note(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_useDiagnosticMsg;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_io_get_num_heartbeats();
x_9 = lean_ctor_get(x_4, 8);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = l_Lean_Name_str___override(x_14, x_1);
x_16 = l_Lean_Core_throwMaxHeartbeat___redArg(x_15, x_2, x_3, x_4);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 9);
x_5 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_));
x_6 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_5, x_4, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_interruptExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 12);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = l_IO_CancelToken_isSet(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg();
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkSystem(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_get_num_heartbeats();
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 8);
lean_dec(x_7);
lean_ctor_set(x_2, 8, x_5);
x_8 = lean_apply_3(x_1, x_2, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get(x_2, 5);
x_15 = lean_ctor_get(x_2, 6);
x_16 = lean_ctor_get(x_2, 7);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_21 = lean_ctor_get(x_2, 12);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_23 = lean_ctor_get(x_2, 13);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_24, 2, x_11);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
lean_ctor_set(x_24, 5, x_14);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_5);
lean_ctor_set(x_24, 9, x_17);
lean_ctor_set(x_24, 10, x_18);
lean_ctor_set(x_24, 11, x_19);
lean_ctor_set(x_24, 12, x_21);
lean_ctor_set(x_24, 13, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*14, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*14 + 1, x_22);
x_25 = lean_apply_3(x_1, x_24, x_3, lean_box(0));
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_2, lean_box(0), x_1);
x_7 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___redArg___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
x_9 = lean_apply_1(x_6, lean_box(0));
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 6);
lean_dec(x_6);
lean_ctor_set(x_4, 6, x_1);
x_7 = lean_st_ref_set(x_2, x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_4, 7);
x_17 = lean_ctor_get(x_4, 8);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
lean_ctor_set(x_18, 5, x_15);
lean_ctor_set(x_18, 6, x_1);
lean_ctor_set(x_18, 7, x_16);
lean_ctor_set(x_18, 8, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_setMessageLog___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_resetMessageLog___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Core_resetMessageLog___redArg___closed__0;
x_4 = l_Lean_Core_resetMessageLog___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_resetMessageLog___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Core_resetMessageLog___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Core_resetMessageLog___redArg___closed__3;
x_4 = l_Lean_Core_setMessageLog___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_resetMessageLog___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getMessageLog___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_5);
x_6 = l_Lean_MessageLog_markAllReported(x_5);
lean_ctor_set(x_3, 6, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get(x_3, 7);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc_ref(x_15);
x_18 = l_Lean_MessageLog_markAllReported(x_15);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_14);
lean_ctor_set(x_19, 6, x_18);
lean_ctor_set(x_19, 7, x_16);
lean_ctor_set(x_19, 8, x_17);
x_20 = lean_st_ref_set(x_1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 8);
x_6 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_ctor_set(x_3, 8, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get(x_3, 7);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_18 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_14);
lean_ctor_set(x_19, 6, x_15);
lean_ctor_set(x_19, 7, x_16);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_ref_set(x_1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_MessageLog_hasErrors(x_5);
lean_dec_ref(x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__0));
x_10 = lean_string_dec_eq(x_6, x_9);
if (x_10 == 0)
{
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__1));
x_12 = lean_string_dec_eq(x_5, x_11);
if (x_12 == 0)
{
return x_12;
}
else
{
return x_1;
}
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__2));
x_14 = lean_string_dec_eq(x_5, x_13);
if (x_14 == 0)
{
return x_14;
}
else
{
return x_1;
}
}
}
case 1:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__3));
x_20 = lean_string_dec_eq(x_18, x_19);
if (x_20 == 0)
{
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__4));
x_22 = lean_string_dec_eq(x_17, x_21);
if (x_22 == 0)
{
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__5));
x_24 = lean_string_dec_eq(x_16, x_23);
if (x_24 == 0)
{
return x_24;
}
else
{
return x_1;
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
default: 
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__6));
x_29 = lean_string_dec_eq(x_27, x_28);
if (x_29 == 0)
{
return x_29;
}
else
{
return x_1;
}
}
default: 
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Core_instMonadLogCoreM___lam__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
if (x_69 == 0)
{
x_5 = x_2;
x_6 = x_3;
x_7 = lean_box(0);
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_1, 4);
x_71 = lean_box(x_69);
x_72 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__3___boxed), 2, 1);
lean_closure_set(x_72, 0, x_71);
lean_inc(x_70);
x_73 = l_Lean_MessageData_hasTag(x_72, x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_5 = x_2;
x_6 = x_3;
x_7 = lean_box(0);
goto block_68;
}
}
block_68:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_ctor_get(x_8, 6);
lean_inc(x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_1, 4, x_16);
x_17 = l_Lean_MessageLog_add(x_1, x_14);
lean_ctor_set(x_8, 6, x_17);
x_18 = lean_st_ref_set(x_6, x_8);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_1, 4);
x_22 = lean_ctor_get(x_5, 6);
x_23 = lean_ctor_get(x_5, 7);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
x_30 = lean_ctor_get(x_8, 6);
x_31 = lean_ctor_get(x_8, 7);
x_32 = lean_ctor_get(x_8, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
lean_inc(x_23);
lean_inc(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_23);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_1, 4, x_34);
x_35 = l_Lean_MessageLog_add(x_1, x_30);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_28);
lean_ctor_set(x_36, 5, x_29);
lean_ctor_set(x_36, 6, x_35);
lean_ctor_set(x_36, 7, x_31);
lean_ctor_set(x_36, 8, x_32);
x_37 = lean_st_ref_set(x_6, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_46 = lean_ctor_get(x_1, 3);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_48 = lean_ctor_get(x_5, 6);
x_49 = lean_ctor_get(x_5, 7);
x_50 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_8, 5);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_8, 6);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_8, 7);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_8, 8);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 lean_ctor_release(x_8, 7);
 lean_ctor_release(x_8, 8);
 x_59 = x_8;
} else {
 lean_dec_ref(x_8);
 x_59 = lean_box(0);
}
lean_inc(x_49);
lean_inc(x_48);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_49);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
x_62 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_62, 0, x_40);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_42);
lean_ctor_set(x_62, 3, x_46);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*5, x_43);
lean_ctor_set_uint8(x_62, sizeof(void*)*5 + 1, x_44);
lean_ctor_set_uint8(x_62, sizeof(void*)*5 + 2, x_45);
x_63 = l_Lean_MessageLog_add(x_62, x_56);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 9, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_51);
lean_ctor_set(x_64, 2, x_52);
lean_ctor_set(x_64, 3, x_53);
lean_ctor_set(x_64, 4, x_54);
lean_ctor_set(x_64, 5, x_55);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_57);
lean_ctor_set(x_64, 8, x_58);
x_65 = lean_st_ref_set(x_6, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLogCoreM___lam__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 8);
x_7 = lean_array_push(x_6, x_1);
lean_ctor_set(x_4, 8, x_7);
x_8 = lean_st_ref_set(x_2, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_16);
lean_ctor_set(x_21, 6, x_17);
lean_ctor_set(x_21, 7, x_18);
lean_ctor_set(x_21, 8, x_20);
x_22 = lean_st_ref_set(x_2, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_IO_addHeartbeats(x_1);
x_8 = lean_apply_4(x_2, x_3, x_4, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsync___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_39; uint8_t x_60; 
x_19 = lean_st_mk_ref(x_1);
x_20 = l_Lean_inheritedTraceOptions;
x_21 = lean_st_ref_get(x_20);
x_22 = lean_st_ref_get(x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_17);
x_25 = l_Lean_diagnostics;
x_26 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_4, x_25);
x_60 = l_Lean_Kernel_isDiagnosticsEnabled(x_23);
lean_dec_ref(x_23);
if (x_60 == 0)
{
if (x_26 == 0)
{
lean_inc(x_19);
x_27 = x_19;
x_28 = lean_box(0);
goto block_38;
}
else
{
x_39 = x_60;
goto block_59;
}
}
else
{
x_39 = x_26;
goto block_59;
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_4, x_29);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_8);
lean_ctor_set(x_31, 6, x_9);
lean_ctor_set(x_31, 7, x_10);
lean_ctor_set(x_31, 8, x_11);
lean_ctor_set(x_31, 9, x_12);
lean_ctor_set(x_31, 10, x_13);
lean_ctor_set(x_31, 11, x_14);
lean_ctor_set(x_31, 12, x_15);
lean_ctor_set(x_31, 13, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_16);
x_32 = l_Lean_Core_withCurrHeartbeats___at___00Lean_Core_wrapAsync_spec__0___redArg(x_24, x_31, x_27);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_st_ref_get(x_19);
lean_dec(x_19);
lean_dec(x_34);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_st_ref_get(x_19);
lean_dec(x_19);
lean_dec(x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
}
else
{
lean_dec(x_19);
return x_32;
}
}
block_59:
{
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_st_ref_take(x_19);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 5);
lean_dec(x_43);
x_44 = l_Lean_Kernel_enableDiag(x_42, x_26);
x_45 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_40, 5, x_45);
lean_ctor_set(x_40, 0, x_44);
x_46 = lean_st_ref_set(x_19, x_40);
lean_inc(x_19);
x_27 = x_19;
x_28 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
x_49 = lean_ctor_get(x_40, 2);
x_50 = lean_ctor_get(x_40, 3);
x_51 = lean_ctor_get(x_40, 4);
x_52 = lean_ctor_get(x_40, 6);
x_53 = lean_ctor_get(x_40, 7);
x_54 = lean_ctor_get(x_40, 8);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_55 = l_Lean_Kernel_enableDiag(x_47, x_26);
x_56 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_51);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_52);
lean_ctor_set(x_57, 7, x_53);
lean_ctor_set(x_57, 8, x_54);
x_58 = lean_st_ref_set(x_19, x_57);
lean_inc(x_19);
x_27 = x_19;
x_28 = lean_box(0);
goto block_38;
}
}
else
{
lean_inc(x_19);
x_27 = x_19;
x_28 = lean_box(0);
goto block_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Core_wrapAsync___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_st_ref_take(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_11, 2);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Name_num___override(x_9, x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_11, 2, x_7);
x_17 = lean_st_ref_set(x_4, x_11);
x_18 = lean_st_ref_get(x_4);
x_19 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = l_Lean_DeclNameGenerator_mkChild(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_st_ref_take(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 3);
lean_dec(x_26);
lean_ctor_set(x_24, 3, x_23);
x_27 = lean_st_ref_set(x_4, x_24);
x_28 = lean_st_ref_get(x_4);
x_29 = lean_io_get_num_heartbeats();
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_28, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_3, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 7);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 8);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 9);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 10);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 11);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 2, x_20);
x_45 = lean_nat_sub(x_29, x_40);
lean_dec(x_29);
x_46 = lean_box(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_47, 0, x_28);
lean_closure_set(x_47, 1, x_45);
lean_closure_set(x_47, 2, x_1);
lean_closure_set(x_47, 3, x_35);
lean_closure_set(x_47, 4, x_33);
lean_closure_set(x_47, 5, x_34);
lean_closure_set(x_47, 6, x_36);
lean_closure_set(x_47, 7, x_37);
lean_closure_set(x_47, 8, x_38);
lean_closure_set(x_47, 9, x_39);
lean_closure_set(x_47, 10, x_40);
lean_closure_set(x_47, 11, x_41);
lean_closure_set(x_47, 12, x_42);
lean_closure_set(x_47, 13, x_43);
lean_closure_set(x_47, 14, x_2);
lean_closure_set(x_47, 15, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
x_51 = lean_ctor_get(x_28, 4);
x_52 = lean_ctor_get(x_28, 5);
x_53 = lean_ctor_get(x_28, 6);
x_54 = lean_ctor_get(x_28, 7);
x_55 = lean_ctor_get(x_28, 8);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_56 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_3, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 6);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 7);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 8);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 9);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 10);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 11);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_14);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_50);
lean_ctor_set(x_68, 2, x_20);
lean_ctor_set(x_68, 3, x_22);
lean_ctor_set(x_68, 4, x_51);
lean_ctor_set(x_68, 5, x_52);
lean_ctor_set(x_68, 6, x_53);
lean_ctor_set(x_68, 7, x_54);
lean_ctor_set(x_68, 8, x_55);
x_69 = lean_nat_sub(x_29, x_63);
lean_dec(x_29);
x_70 = lean_box(x_67);
x_71 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_71, 0, x_68);
lean_closure_set(x_71, 1, x_69);
lean_closure_set(x_71, 2, x_1);
lean_closure_set(x_71, 3, x_58);
lean_closure_set(x_71, 4, x_56);
lean_closure_set(x_71, 5, x_57);
lean_closure_set(x_71, 6, x_59);
lean_closure_set(x_71, 7, x_60);
lean_closure_set(x_71, 8, x_61);
lean_closure_set(x_71, 9, x_62);
lean_closure_set(x_71, 10, x_63);
lean_closure_set(x_71, 11, x_64);
lean_closure_set(x_71, 12, x_65);
lean_closure_set(x_71, 13, x_66);
lean_closure_set(x_71, 14, x_2);
lean_closure_set(x_71, 15, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_73 = lean_ctor_get(x_24, 0);
x_74 = lean_ctor_get(x_24, 1);
x_75 = lean_ctor_get(x_24, 2);
x_76 = lean_ctor_get(x_24, 4);
x_77 = lean_ctor_get(x_24, 5);
x_78 = lean_ctor_get(x_24, 6);
x_79 = lean_ctor_get(x_24, 7);
x_80 = lean_ctor_get(x_24, 8);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_24);
x_81 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_74);
lean_ctor_set(x_81, 2, x_75);
lean_ctor_set(x_81, 3, x_23);
lean_ctor_set(x_81, 4, x_76);
lean_ctor_set(x_81, 5, x_77);
lean_ctor_set(x_81, 6, x_78);
lean_ctor_set(x_81, 7, x_79);
lean_ctor_set(x_81, 8, x_80);
x_82 = lean_st_ref_set(x_4, x_81);
x_83 = lean_st_ref_get(x_4);
x_84 = lean_io_get_num_heartbeats();
x_85 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 4);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_83, 5);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_83, 6);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_83, 7);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_83, 8);
lean_inc_ref(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 lean_ctor_release(x_83, 6);
 lean_ctor_release(x_83, 7);
 lean_ctor_release(x_83, 8);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_3, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 6);
lean_inc(x_98);
x_99 = lean_ctor_get(x_3, 7);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 8);
lean_inc(x_100);
x_101 = lean_ctor_get(x_3, 9);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 10);
lean_inc(x_102);
x_103 = lean_ctor_get(x_3, 11);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_14);
if (lean_is_scalar(x_92)) {
 x_105 = lean_alloc_ctor(0, 9, 0);
} else {
 x_105 = x_92;
}
lean_ctor_set(x_105, 0, x_85);
lean_ctor_set(x_105, 1, x_86);
lean_ctor_set(x_105, 2, x_20);
lean_ctor_set(x_105, 3, x_22);
lean_ctor_set(x_105, 4, x_87);
lean_ctor_set(x_105, 5, x_88);
lean_ctor_set(x_105, 6, x_89);
lean_ctor_set(x_105, 7, x_90);
lean_ctor_set(x_105, 8, x_91);
x_106 = lean_nat_sub(x_84, x_100);
lean_dec(x_84);
x_107 = lean_box(x_104);
x_108 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_108, 0, x_105);
lean_closure_set(x_108, 1, x_106);
lean_closure_set(x_108, 2, x_1);
lean_closure_set(x_108, 3, x_95);
lean_closure_set(x_108, 4, x_93);
lean_closure_set(x_108, 5, x_94);
lean_closure_set(x_108, 6, x_96);
lean_closure_set(x_108, 7, x_97);
lean_closure_set(x_108, 8, x_98);
lean_closure_set(x_108, 9, x_99);
lean_closure_set(x_108, 10, x_100);
lean_closure_set(x_108, 11, x_101);
lean_closure_set(x_108, 12, x_102);
lean_closure_set(x_108, 13, x_103);
lean_closure_set(x_108, 14, x_2);
lean_closure_set(x_108, 15, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_110 = lean_ctor_get(x_20, 0);
x_111 = lean_ctor_get(x_20, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_20);
x_112 = lean_st_ref_take(x_4);
x_113 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 2);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_112, 4);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_112, 5);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_112, 6);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_112, 7);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_112, 8);
lean_inc_ref(x_120);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 lean_ctor_release(x_112, 6);
 lean_ctor_release(x_112, 7);
 lean_ctor_release(x_112, 8);
 x_121 = x_112;
} else {
 lean_dec_ref(x_112);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_115);
lean_ctor_set(x_122, 3, x_111);
lean_ctor_set(x_122, 4, x_116);
lean_ctor_set(x_122, 5, x_117);
lean_ctor_set(x_122, 6, x_118);
lean_ctor_set(x_122, 7, x_119);
lean_ctor_set(x_122, 8, x_120);
x_123 = lean_st_ref_set(x_4, x_122);
x_124 = lean_st_ref_get(x_4);
x_125 = lean_io_get_num_heartbeats();
x_126 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 4);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_124, 5);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_124, 6);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_124, 7);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_124, 8);
lean_inc_ref(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 lean_ctor_release(x_124, 6);
 lean_ctor_release(x_124, 7);
 lean_ctor_release(x_124, 8);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_3, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 6);
lean_inc(x_139);
x_140 = lean_ctor_get(x_3, 7);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 8);
lean_inc(x_141);
x_142 = lean_ctor_get(x_3, 9);
lean_inc(x_142);
x_143 = lean_ctor_get(x_3, 10);
lean_inc(x_143);
x_144 = lean_ctor_get(x_3, 11);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_14);
lean_ctor_set(x_146, 1, x_15);
if (lean_is_scalar(x_133)) {
 x_147 = lean_alloc_ctor(0, 9, 0);
} else {
 x_147 = x_133;
}
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_127);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_110);
lean_ctor_set(x_147, 4, x_128);
lean_ctor_set(x_147, 5, x_129);
lean_ctor_set(x_147, 6, x_130);
lean_ctor_set(x_147, 7, x_131);
lean_ctor_set(x_147, 8, x_132);
x_148 = lean_nat_sub(x_125, x_141);
lean_dec(x_125);
x_149 = lean_box(x_145);
x_150 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_150, 0, x_147);
lean_closure_set(x_150, 1, x_148);
lean_closure_set(x_150, 2, x_1);
lean_closure_set(x_150, 3, x_136);
lean_closure_set(x_150, 4, x_134);
lean_closure_set(x_150, 5, x_135);
lean_closure_set(x_150, 6, x_137);
lean_closure_set(x_150, 7, x_138);
lean_closure_set(x_150, 8, x_139);
lean_closure_set(x_150, 9, x_140);
lean_closure_set(x_150, 10, x_141);
lean_closure_set(x_150, 11, x_142);
lean_closure_set(x_150, 12, x_143);
lean_closure_set(x_150, 13, x_144);
lean_closure_set(x_150, 14, x_2);
lean_closure_set(x_150, 15, x_149);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_152 = lean_ctor_get(x_11, 0);
x_153 = lean_ctor_get(x_11, 1);
x_154 = lean_ctor_get(x_11, 3);
x_155 = lean_ctor_get(x_11, 4);
x_156 = lean_ctor_get(x_11, 5);
x_157 = lean_ctor_get(x_11, 6);
x_158 = lean_ctor_get(x_11, 7);
x_159 = lean_ctor_get(x_11, 8);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_160 = l_Lean_Name_num___override(x_9, x_10);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_add(x_10, x_161);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_162);
x_163 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_153);
lean_ctor_set(x_163, 2, x_7);
lean_ctor_set(x_163, 3, x_154);
lean_ctor_set(x_163, 4, x_155);
lean_ctor_set(x_163, 5, x_156);
lean_ctor_set(x_163, 6, x_157);
lean_ctor_set(x_163, 7, x_158);
lean_ctor_set(x_163, 8, x_159);
x_164 = lean_st_ref_set(x_4, x_163);
x_165 = lean_st_ref_get(x_4);
x_166 = lean_ctor_get(x_165, 3);
lean_inc_ref(x_166);
lean_dec(x_165);
x_167 = l_Lean_DeclNameGenerator_mkChild(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
x_171 = lean_st_ref_take(x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_171, 4);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_171, 5);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_171, 6);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_171, 7);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_171, 8);
lean_inc_ref(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 lean_ctor_release(x_171, 6);
 lean_ctor_release(x_171, 7);
 lean_ctor_release(x_171, 8);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 9, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_173);
lean_ctor_set(x_181, 2, x_174);
lean_ctor_set(x_181, 3, x_169);
lean_ctor_set(x_181, 4, x_175);
lean_ctor_set(x_181, 5, x_176);
lean_ctor_set(x_181, 6, x_177);
lean_ctor_set(x_181, 7, x_178);
lean_ctor_set(x_181, 8, x_179);
x_182 = lean_st_ref_set(x_4, x_181);
x_183 = lean_st_ref_get(x_4);
x_184 = lean_io_get_num_heartbeats();
x_185 = lean_ctor_get(x_183, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 4);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_183, 5);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_183, 6);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_183, 7);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_183, 8);
lean_inc_ref(x_191);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 lean_ctor_release(x_183, 5);
 lean_ctor_release(x_183, 6);
 lean_ctor_release(x_183, 7);
 lean_ctor_release(x_183, 8);
 x_192 = x_183;
} else {
 lean_dec_ref(x_183);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_3, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_3, 5);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 6);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 7);
lean_inc(x_199);
x_200 = lean_ctor_get(x_3, 8);
lean_inc(x_200);
x_201 = lean_ctor_get(x_3, 9);
lean_inc(x_201);
x_202 = lean_ctor_get(x_3, 10);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 11);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
if (lean_is_scalar(x_170)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_170;
}
lean_ctor_set(x_205, 0, x_160);
lean_ctor_set(x_205, 1, x_161);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 9, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_185);
lean_ctor_set(x_206, 1, x_186);
lean_ctor_set(x_206, 2, x_205);
lean_ctor_set(x_206, 3, x_168);
lean_ctor_set(x_206, 4, x_187);
lean_ctor_set(x_206, 5, x_188);
lean_ctor_set(x_206, 6, x_189);
lean_ctor_set(x_206, 7, x_190);
lean_ctor_set(x_206, 8, x_191);
x_207 = lean_nat_sub(x_184, x_200);
lean_dec(x_184);
x_208 = lean_box(x_204);
x_209 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_209, 0, x_206);
lean_closure_set(x_209, 1, x_207);
lean_closure_set(x_209, 2, x_1);
lean_closure_set(x_209, 3, x_195);
lean_closure_set(x_209, 4, x_193);
lean_closure_set(x_209, 5, x_194);
lean_closure_set(x_209, 6, x_196);
lean_closure_set(x_209, 7, x_197);
lean_closure_set(x_209, 8, x_198);
lean_closure_set(x_209, 9, x_199);
lean_closure_set(x_209, 10, x_200);
lean_closure_set(x_209, 11, x_201);
lean_closure_set(x_209, 12, x_202);
lean_closure_set(x_209, 13, x_203);
lean_closure_set(x_209, 14, x_2);
lean_closure_set(x_209, 15, x_208);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_211 = lean_ctor_get(x_7, 0);
x_212 = lean_ctor_get(x_7, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_7);
x_213 = lean_st_ref_take(x_4);
x_214 = lean_ctor_get(x_213, 0);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 3);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_213, 4);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_213, 5);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_213, 6);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_213, 7);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_213, 8);
lean_inc_ref(x_221);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 lean_ctor_release(x_213, 6);
 lean_ctor_release(x_213, 7);
 lean_ctor_release(x_213, 8);
 x_222 = x_213;
} else {
 lean_dec_ref(x_213);
 x_222 = lean_box(0);
}
lean_inc(x_212);
lean_inc(x_211);
x_223 = l_Lean_Name_num___override(x_211, x_212);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_212, x_224);
lean_dec(x_212);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_211);
lean_ctor_set(x_226, 1, x_225);
if (lean_is_scalar(x_222)) {
 x_227 = lean_alloc_ctor(0, 9, 0);
} else {
 x_227 = x_222;
}
lean_ctor_set(x_227, 0, x_214);
lean_ctor_set(x_227, 1, x_215);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set(x_227, 3, x_216);
lean_ctor_set(x_227, 4, x_217);
lean_ctor_set(x_227, 5, x_218);
lean_ctor_set(x_227, 6, x_219);
lean_ctor_set(x_227, 7, x_220);
lean_ctor_set(x_227, 8, x_221);
x_228 = lean_st_ref_set(x_4, x_227);
x_229 = lean_st_ref_get(x_4);
x_230 = lean_ctor_get(x_229, 3);
lean_inc_ref(x_230);
lean_dec(x_229);
x_231 = l_Lean_DeclNameGenerator_mkChild(x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = lean_st_ref_take(x_4);
x_236 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 2);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_235, 4);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_235, 5);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_235, 6);
lean_inc_ref(x_241);
x_242 = lean_ctor_get(x_235, 7);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_235, 8);
lean_inc_ref(x_243);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 lean_ctor_release(x_235, 5);
 lean_ctor_release(x_235, 6);
 lean_ctor_release(x_235, 7);
 lean_ctor_release(x_235, 8);
 x_244 = x_235;
} else {
 lean_dec_ref(x_235);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 9, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_236);
lean_ctor_set(x_245, 1, x_237);
lean_ctor_set(x_245, 2, x_238);
lean_ctor_set(x_245, 3, x_233);
lean_ctor_set(x_245, 4, x_239);
lean_ctor_set(x_245, 5, x_240);
lean_ctor_set(x_245, 6, x_241);
lean_ctor_set(x_245, 7, x_242);
lean_ctor_set(x_245, 8, x_243);
x_246 = lean_st_ref_set(x_4, x_245);
x_247 = lean_st_ref_get(x_4);
x_248 = lean_io_get_num_heartbeats();
x_249 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_249);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 4);
lean_inc_ref(x_251);
x_252 = lean_ctor_get(x_247, 5);
lean_inc_ref(x_252);
x_253 = lean_ctor_get(x_247, 6);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_247, 7);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_247, 8);
lean_inc_ref(x_255);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 lean_ctor_release(x_247, 4);
 lean_ctor_release(x_247, 5);
 lean_ctor_release(x_247, 6);
 lean_ctor_release(x_247, 7);
 lean_ctor_release(x_247, 8);
 x_256 = x_247;
} else {
 lean_dec_ref(x_247);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_258);
x_259 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_3, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_3, 5);
lean_inc(x_261);
x_262 = lean_ctor_get(x_3, 6);
lean_inc(x_262);
x_263 = lean_ctor_get(x_3, 7);
lean_inc(x_263);
x_264 = lean_ctor_get(x_3, 8);
lean_inc(x_264);
x_265 = lean_ctor_get(x_3, 9);
lean_inc(x_265);
x_266 = lean_ctor_get(x_3, 10);
lean_inc(x_266);
x_267 = lean_ctor_get(x_3, 11);
lean_inc(x_267);
x_268 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
lean_dec_ref(x_3);
if (lean_is_scalar(x_234)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_234;
}
lean_ctor_set(x_269, 0, x_223);
lean_ctor_set(x_269, 1, x_224);
if (lean_is_scalar(x_256)) {
 x_270 = lean_alloc_ctor(0, 9, 0);
} else {
 x_270 = x_256;
}
lean_ctor_set(x_270, 0, x_249);
lean_ctor_set(x_270, 1, x_250);
lean_ctor_set(x_270, 2, x_269);
lean_ctor_set(x_270, 3, x_232);
lean_ctor_set(x_270, 4, x_251);
lean_ctor_set(x_270, 5, x_252);
lean_ctor_set(x_270, 6, x_253);
lean_ctor_set(x_270, 7, x_254);
lean_ctor_set(x_270, 8, x_255);
x_271 = lean_nat_sub(x_248, x_264);
lean_dec(x_248);
x_272 = lean_box(x_268);
x_273 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 18, 16);
lean_closure_set(x_273, 0, x_270);
lean_closure_set(x_273, 1, x_271);
lean_closure_set(x_273, 2, x_1);
lean_closure_set(x_273, 3, x_259);
lean_closure_set(x_273, 4, x_257);
lean_closure_set(x_273, 5, x_258);
lean_closure_set(x_273, 6, x_260);
lean_closure_set(x_273, 7, x_261);
lean_closure_set(x_273, 8, x_262);
lean_closure_set(x_273, 9, x_263);
lean_closure_set(x_273, 10, x_264);
lean_closure_set(x_273, 11, x_265);
lean_closure_set(x_273, 12, x_266);
lean_closure_set(x_273, 13, x_267);
lean_closure_set(x_273, 14, x_2);
lean_closure_set(x_273, 15, x_272);
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsync___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Core_initFn___closed__2_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_));
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Core_initFn___closed__1_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_));
x_3 = l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__8));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__22));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__25));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__28));
x_3 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__14));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__5));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37;
x_2 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38;
x_2 = ((lean_object*)(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__2));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_mkSnapshot_x3f___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 8);
lean_inc_ref(x_8);
lean_dec_ref(x_3);
x_27 = lean_string_utf8_byte_size(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_43; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_2, 5);
lean_inc(x_32);
lean_dec_ref(x_2);
x_43 = l_Lean_Syntax_getPos_x3f(x_32, x_29);
lean_dec(x_32);
if (lean_obj_tag(x_43) == 0)
{
x_33 = x_28;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_33 = x_44;
goto block_42;
}
block_42:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = l_Lean_FileMap_toPosition(x_31, x_33);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = 0;
x_37 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_29);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 1, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 2, x_29);
x_41 = l_Lean_MessageLog_add(x_40, x_7);
x_18 = x_41;
x_19 = lean_box(0);
goto block_26;
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = x_7;
x_19 = lean_box(0);
goto block_26;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_26:
{
uint8_t x_20; 
x_20 = l_Lean_MessageLog_hasUnreported(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = l_Lean_PersistentArray_isEmpty___redArg(x_21);
if (x_22 == 0)
{
x_9 = lean_box(0);
x_10 = x_18;
x_11 = x_22;
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = l_Array_isEmpty___redArg(x_8);
if (x_23 == 0)
{
x_9 = lean_box(0);
x_10 = x_18;
x_11 = x_23;
goto block_17;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_18);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_24 = lean_box(0);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
x_9 = lean_box(0);
x_10 = x_18;
x_11 = x_25;
goto block_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_mkSnapshot_x3f(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__0));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__1));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__2));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__3));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__4));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__5));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__6));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_107; uint8_t x_123; 
x_98 = 2;
x_123 = l_Lean_instBEqMessageSeverity_beq(x_3, x_98);
if (x_123 == 0)
{
x_107 = x_123;
goto block_122;
}
else
{
uint8_t x_124; 
lean_inc_ref(x_2);
x_124 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_107 = x_124;
goto block_122;
}
block_47:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_st_ref_take(x_16);
x_19 = lean_ctor_get(x_15, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 7);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_18, 6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 2, x_4);
x_26 = l_Lean_MessageLog_add(x_25, x_22);
lean_ctor_set(x_18, 6, x_26);
x_27 = lean_st_ref_set(x_16, x_18);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
x_37 = lean_ctor_get(x_18, 7);
x_38 = lean_ctor_get(x_18, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_20);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
x_41 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_10);
lean_ctor_set(x_41, 2, x_14);
lean_ctor_set(x_41, 3, x_11);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_41, sizeof(void*)*5 + 2, x_4);
x_42 = l_Lean_MessageLog_add(x_41, x_36);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set(x_43, 3, x_33);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_35);
lean_ctor_set(x_43, 6, x_42);
lean_ctor_set(x_43, 7, x_37);
lean_ctor_set(x_43, 8, x_38);
x_44 = lean_st_ref_set(x_16, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
block_74:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_57 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_56, x_5, x_6);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_51);
x_60 = l_Lean_FileMap_toPosition(x_51, x_52);
lean_dec(x_52);
x_61 = l_Lean_FileMap_toPosition(x_51, x_55);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
if (x_53 == 0)
{
lean_free_object(x_57);
lean_dec_ref(x_48);
x_8 = x_59;
x_9 = x_49;
x_10 = x_60;
x_11 = x_63;
x_12 = x_50;
x_13 = x_54;
x_14 = x_62;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_64; 
lean_inc(x_59);
x_64 = l_Lean_MessageData_hasTag(x_48, x_59);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_49);
lean_dec_ref(x_5);
x_65 = lean_box(0);
lean_ctor_set(x_57, 0, x_65);
return x_57;
}
else
{
lean_free_object(x_57);
x_8 = x_59;
x_9 = x_49;
x_10 = x_60;
x_11 = x_63;
x_12 = x_50;
x_13 = x_54;
x_14 = x_62;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
lean_inc_ref(x_51);
x_67 = l_Lean_FileMap_toPosition(x_51, x_52);
lean_dec(x_52);
x_68 = l_Lean_FileMap_toPosition(x_51, x_55);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
if (x_53 == 0)
{
lean_dec_ref(x_48);
x_8 = x_66;
x_9 = x_49;
x_10 = x_67;
x_11 = x_70;
x_12 = x_50;
x_13 = x_54;
x_14 = x_69;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_71; 
lean_inc(x_66);
x_71 = l_Lean_MessageData_hasTag(x_48, x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_69);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_49);
lean_dec_ref(x_5);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
x_8 = x_66;
x_9 = x_49;
x_10 = x_67;
x_11 = x_70;
x_12 = x_50;
x_13 = x_54;
x_14 = x_69;
x_15 = x_5;
x_16 = x_6;
x_17 = lean_box(0);
goto block_47;
}
}
}
}
block_85:
{
lean_object* x_83; 
x_83 = l_Lean_Syntax_getTailPos_x3f(x_77, x_78);
lean_dec(x_77);
if (lean_obj_tag(x_83) == 0)
{
lean_inc(x_82);
x_48 = x_75;
x_49 = x_76;
x_50 = x_78;
x_51 = x_79;
x_52 = x_82;
x_53 = x_81;
x_54 = x_80;
x_55 = x_82;
goto block_74;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_48 = x_75;
x_49 = x_76;
x_50 = x_78;
x_51 = x_79;
x_52 = x_82;
x_53 = x_81;
x_54 = x_80;
x_55 = x_84;
goto block_74;
}
}
block_97:
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_replaceRef(x_1, x_87);
lean_dec(x_87);
x_94 = l_Lean_Syntax_getPos_x3f(x_93, x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_unsigned_to_nat(0u);
x_75 = x_86;
x_76 = x_88;
x_77 = x_93;
x_78 = x_89;
x_79 = x_90;
x_80 = x_92;
x_81 = x_91;
x_82 = x_95;
goto block_85;
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec_ref(x_94);
x_75 = x_86;
x_76 = x_88;
x_77 = x_93;
x_78 = x_89;
x_79 = x_90;
x_80 = x_92;
x_81 = x_91;
x_82 = x_96;
goto block_85;
}
}
block_106:
{
if (x_105 == 0)
{
x_86 = x_102;
x_87 = x_99;
x_88 = x_100;
x_89 = x_104;
x_90 = x_101;
x_91 = x_103;
x_92 = x_3;
goto block_97;
}
else
{
x_86 = x_102;
x_87 = x_99;
x_88 = x_100;
x_89 = x_104;
x_90 = x_101;
x_91 = x_103;
x_92 = x_98;
goto block_97;
}
}
block_122:
{
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_108 = lean_ctor_get(x_5, 0);
x_109 = lean_ctor_get(x_5, 1);
x_110 = lean_ctor_get(x_5, 2);
x_111 = lean_ctor_get(x_5, 5);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_113 = lean_box(x_107);
x_114 = lean_box(x_112);
x_115 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___lam__0___boxed), 3, 2);
lean_closure_set(x_115, 0, x_113);
lean_closure_set(x_115, 1, x_114);
x_116 = 1;
x_117 = l_Lean_instBEqMessageSeverity_beq(x_3, x_116);
if (x_117 == 0)
{
lean_inc_ref(x_109);
lean_inc_ref(x_108);
lean_inc(x_111);
x_99 = x_111;
x_100 = x_108;
x_101 = x_109;
x_102 = x_115;
x_103 = x_112;
x_104 = x_107;
x_105 = x_117;
goto block_106;
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = l_Lean_warningAsError;
x_119 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_110, x_118);
lean_inc_ref(x_109);
lean_inc_ref(x_108);
lean_inc(x_111);
x_99 = x_111;
x_100 = x_108;
x_101 = x_109;
x_102 = x_115;
x_103 = x_112;
x_104 = x_107;
x_105 = x_119;
goto block_106;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9_spec__18(x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 2;
x_6 = 0;
x_7 = l_Lean_log___at___00Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1_spec__9(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_nat_dec_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_4);
x_8 = lean_uint64_of_nat(x_5);
x_9 = lean_uint64_of_nat(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_4, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_22);
lean_dec(x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_nat_dec_eq(x_13, x_15);
if (x_17 == 0)
{
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_array_get_size(x_1);
x_32 = lean_uint64_of_nat(x_29);
x_33 = lean_uint64_of_nat(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = lean_uint64_of_nat(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_array_uset(x_6, x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(x_2, x_3, x_24);
x_40 = lean_array_uset(x_38, x_23, x_39);
lean_ctor_set(x_1, 1, x_40);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_array_get_size(x_42);
x_46 = lean_uint64_of_nat(x_43);
x_47 = lean_uint64_of_nat(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_45);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_42, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_41, x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_array_uset(x_42, x_59, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_42, x_59, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(x_2, x_3, x_60);
x_78 = lean_array_uset(x_76, x_59, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_30 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_14);
x_35 = l_Lean_Syntax_getPos_x3f(x_30, x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_unsigned_to_nat(0u);
x_31 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_31 = x_37;
goto block_34;
}
block_29:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_22 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_10, x_20, x_21);
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_10, x_20, x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_11;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
goto _start;
}
block_34:
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getTailPos_x3f(x_30, x_1);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_inc(x_31);
x_18 = x_31;
x_19 = x_31;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_33;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_box(0);
x_31 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_15);
x_36 = l_Lean_Syntax_getPos_x3f(x_31, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(0u);
x_32 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_32 = x_38;
goto block_35;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_11, x_21, x_22);
x_24 = lean_array_push(x_23, x_16);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_11, x_21, x_24);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_12;
}
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg(x_1, x_2, x_3, x_28, x_26, x_6);
return x_29;
}
block_35:
{
lean_object* x_33; 
x_33 = l_Lean_Syntax_getTailPos_x3f(x_31, x_1);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_inc(x_32);
x_19 = x_32;
x_20 = x_32;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_19 = x_32;
x_20 = x_34;
goto block_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_array_size(x_9);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20(x_1, x_2, x_9, x_12, x_13, x_11, x_5, x_6);
lean_dec_ref(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_18);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_19; 
lean_inc_ref(x_17);
lean_dec(x_16);
lean_free_object(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_21);
lean_dec(x_20);
lean_free_object(x_3);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_free_object(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20(x_1, x_2, x_29, x_32, x_33, x_31, x_5, x_6);
lean_dec_ref(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_37);
lean_dec(x_35);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec_ref(x_37);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
x_50 = lean_array_size(x_47);
x_51 = 0;
x_52 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21(x_1, x_47, x_50, x_51, x_49, x_5, x_6);
lean_dec_ref(x_47);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_ctor_set(x_3, 0, x_56);
lean_ctor_set(x_52, 0, x_3);
return x_52;
}
else
{
lean_object* x_57; 
lean_inc_ref(x_55);
lean_dec(x_54);
lean_free_object(x_3);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_ctor_set(x_3, 0, x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_3);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_inc_ref(x_59);
lean_dec(x_58);
lean_free_object(x_3);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec_ref(x_59);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_free_object(x_3);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
x_70 = lean_array_size(x_67);
x_71 = 0;
x_72 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21(x_1, x_67, x_70, x_71, x_69, x_5, x_6);
lean_dec_ref(x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_73, 0);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_inc_ref(x_75);
lean_dec(x_73);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec_ref(x_75);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(x_1, x_2, x_15, x_13, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
lean_free_object(x_16);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_13);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_box(0);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_29);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_13);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_array_uget(x_3, x_5);
lean_inc(x_36);
x_38 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(x_1, x_2, x_37, x_36, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_40);
lean_dec(x_36);
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec_ref(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_36);
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__20(x_10, x_2, x_3, x_11, x_12, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_box(0);
x_30 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_14);
x_35 = l_Lean_Syntax_getPos_x3f(x_30, x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_unsigned_to_nat(0u);
x_31 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_31 = x_37;
goto block_34;
}
block_29:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_22 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_10, x_20, x_21);
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_10, x_20, x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_11;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
goto _start;
}
block_34:
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getTailPos_x3f(x_30, x_1);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_inc(x_31);
x_18 = x_31;
x_19 = x_31;
goto block_29;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_33;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg(x_8, x_2, x_9, x_10, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_box(0);
x_31 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_15);
x_36 = l_Lean_Syntax_getPos_x3f(x_31, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_unsigned_to_nat(0u);
x_32 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_32 = x_38;
goto block_35;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_11, x_21, x_22);
x_24 = lean_array_push(x_23, x_16);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_11, x_21, x_24);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_12;
}
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_4, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg(x_1, x_2, x_3, x_28, x_26, x_6);
return x_29;
}
block_35:
{
lean_object* x_33; 
x_33 = l_Lean_Syntax_getTailPos_x3f(x_31, x_1);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_inc(x_32);
x_19 = x_32;
x_20 = x_32;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_19 = x_32;
x_20 = x_34;
goto block_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_9 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10(x_1, x_3, x_7, x_3, x_4, x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_array_size(x_8);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11(x_1, x_8, x_16, x_17, x_15, x_4, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; 
lean_inc_ref(x_21);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_25);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 0);
lean_inc(x_33);
lean_dec(x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_size(x_8);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11(x_1, x_8, x_39, x_40, x_38, x_4, x_5);
lean_dec_ref(x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_8);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__6(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; 
lean_free_object(x_5);
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__0));
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
return x_1;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__1));
x_14 = lean_string_dec_eq(x_7, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__2));
x_16 = lean_string_dec_eq(x_7, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_6, 1);
x_21 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__3));
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
return x_1;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__4));
x_24 = lean_string_dec_eq(x_19, x_23);
if (x_24 == 0)
{
return x_1;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__5));
x_26 = lean_string_dec_eq(x_18, x_25);
if (x_26 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_string_dec_eq(x_27, x_3);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0(x_5, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; double x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_box(0);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_26 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_27 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_float(x_27, sizeof(void*)*2, x_25);
lean_ctor_set_float(x_27, sizeof(void*)*2 + 8, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_15);
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_31 = lean_box(0);
x_32 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__6));
x_33 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0));
x_34 = l_Lean_MessageData_nil;
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set_tag(x_18, 8);
lean_ctor_set(x_18, 1, x_35);
lean_ctor_set(x_18, 0, x_33);
x_36 = 0;
lean_inc_ref(x_29);
lean_inc_ref(x_28);
x_37 = l_Lean_Elab_mkMessageCore(x_28, x_29, x_18, x_36, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_30 == 0)
{
lean_inc_ref(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_37, 4);
lean_inc(x_93);
x_94 = lean_box(x_1);
x_95 = lean_box(x_30);
x_96 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0___boxed), 4, 3);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_95);
lean_closure_set(x_96, 2, x_32);
x_97 = l_Lean_MessageData_hasTag(x_96, x_93);
if (x_97 == 0)
{
lean_dec_ref(x_37);
lean_dec(x_20);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_inc_ref(x_6);
x_38 = x_6;
x_39 = x_7;
x_40 = lean_box(0);
goto block_92;
}
}
block_92:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_take(x_39);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_37, 4);
x_44 = lean_ctor_get(x_38, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 7);
lean_inc(x_45);
lean_dec_ref(x_38);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_41, 6);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_37, 4, x_49);
x_50 = l_Lean_MessageLog_add(x_37, x_47);
lean_ctor_set(x_41, 6, x_50);
x_51 = lean_st_ref_set(x_39, x_41);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
x_54 = lean_ctor_get(x_41, 2);
x_55 = lean_ctor_get(x_41, 3);
x_56 = lean_ctor_get(x_41, 4);
x_57 = lean_ctor_get(x_41, 5);
x_58 = lean_ctor_get(x_41, 6);
x_59 = lean_ctor_get(x_41, 7);
x_60 = lean_ctor_get(x_41, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
if (lean_is_scalar(x_20)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_20;
}
lean_ctor_set(x_61, 0, x_44);
lean_ctor_set(x_61, 1, x_45);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_43);
lean_ctor_set(x_37, 4, x_62);
x_63 = l_Lean_MessageLog_add(x_37, x_58);
x_64 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_54);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set(x_64, 4, x_56);
lean_ctor_set(x_64, 5, x_57);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_59);
lean_ctor_set(x_64, 8, x_60);
x_65 = lean_st_ref_set(x_39, x_64);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
x_68 = lean_ctor_get(x_37, 2);
x_69 = lean_ctor_get_uint8(x_37, sizeof(void*)*5);
x_70 = lean_ctor_get_uint8(x_37, sizeof(void*)*5 + 1);
x_71 = lean_ctor_get_uint8(x_37, sizeof(void*)*5 + 2);
x_72 = lean_ctor_get(x_37, 3);
x_73 = lean_ctor_get(x_37, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_74 = lean_ctor_get(x_38, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 7);
lean_inc(x_75);
lean_dec_ref(x_38);
x_76 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_41, 4);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_41, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_41, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_41, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_41, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 lean_ctor_release(x_41, 7);
 lean_ctor_release(x_41, 8);
 x_85 = x_41;
} else {
 lean_dec_ref(x_41);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_20;
}
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_75);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_73);
x_88 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_67);
lean_ctor_set(x_88, 2, x_68);
lean_ctor_set(x_88, 3, x_72);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*5, x_69);
lean_ctor_set_uint8(x_88, sizeof(void*)*5 + 1, x_70);
lean_ctor_set_uint8(x_88, sizeof(void*)*5 + 2, x_71);
x_89 = l_Lean_MessageLog_add(x_88, x_82);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 9, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_90, 2, x_78);
lean_ctor_set(x_90, 3, x_79);
lean_ctor_set(x_90, 4, x_80);
lean_ctor_set(x_90, 5, x_81);
lean_ctor_set(x_90, 6, x_89);
lean_ctor_set(x_90, 7, x_83);
lean_ctor_set(x_90, 8, x_84);
x_91 = lean_st_ref_set(x_39, x_90);
x_9 = x_31;
x_10 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; double x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_98 = lean_ctor_get(x_18, 0);
x_99 = lean_ctor_get(x_18, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_18);
x_100 = lean_box(0);
x_101 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_102 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_103 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_float(x_103, sizeof(void*)*2, x_101);
lean_ctor_set_float(x_103, sizeof(void*)*2 + 8, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 16, x_15);
x_104 = lean_ctor_get(x_6, 0);
x_105 = lean_ctor_get(x_6, 1);
x_106 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_107 = lean_box(0);
x_108 = ((lean_object*)(l_Lean_Core_instMonadLogCoreM___lam__3___closed__6));
x_109 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg___closed__0));
x_110 = l_Lean_MessageData_nil;
x_111 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_19);
x_112 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = 0;
lean_inc_ref(x_105);
lean_inc_ref(x_104);
x_114 = l_Lean_Elab_mkMessageCore(x_104, x_105, x_112, x_113, x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_106 == 0)
{
lean_inc_ref(x_6);
x_115 = x_6;
x_116 = x_7;
x_117 = lean_box(0);
goto block_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_114, 4);
lean_inc(x_147);
x_148 = lean_box(x_1);
x_149 = lean_box(x_106);
x_150 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___lam__0___boxed), 4, 3);
lean_closure_set(x_150, 0, x_148);
lean_closure_set(x_150, 1, x_149);
lean_closure_set(x_150, 2, x_108);
x_151 = l_Lean_MessageData_hasTag(x_150, x_147);
if (x_151 == 0)
{
lean_dec_ref(x_114);
lean_dec(x_20);
x_9 = x_107;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_inc_ref(x_6);
x_115 = x_6;
x_116 = x_7;
x_117 = lean_box(0);
goto block_146;
}
}
block_146:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_118 = lean_st_ref_take(x_116);
x_119 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_114, 2);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_114, sizeof(void*)*5);
x_123 = lean_ctor_get_uint8(x_114, sizeof(void*)*5 + 1);
x_124 = lean_ctor_get_uint8(x_114, sizeof(void*)*5 + 2);
x_125 = lean_ctor_get(x_114, 3);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_114, 4);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_115, 6);
lean_inc(x_128);
x_129 = lean_ctor_get(x_115, 7);
lean_inc(x_129);
lean_dec_ref(x_115);
x_130 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_118, 2);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_118, 3);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_118, 4);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_118, 5);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_118, 7);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_118, 8);
lean_inc_ref(x_138);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 x_139 = x_118;
} else {
 lean_dec_ref(x_118);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_20;
}
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_129);
x_141 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 5, 3);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_119);
lean_ctor_set(x_142, 1, x_120);
lean_ctor_set(x_142, 2, x_121);
lean_ctor_set(x_142, 3, x_125);
lean_ctor_set(x_142, 4, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*5, x_122);
lean_ctor_set_uint8(x_142, sizeof(void*)*5 + 1, x_123);
lean_ctor_set_uint8(x_142, sizeof(void*)*5 + 2, x_124);
x_143 = l_Lean_MessageLog_add(x_142, x_136);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 9, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_131);
lean_ctor_set(x_144, 2, x_132);
lean_ctor_set(x_144, 3, x_133);
lean_ctor_set(x_144, 4, x_134);
lean_ctor_set(x_144, 5, x_135);
lean_ctor_set(x_144, 6, x_143);
lean_ctor_set(x_144, 7, x_137);
lean_ctor_set(x_144, 8, x_138);
x_145 = lean_st_ref_set(x_116, x_144);
x_9 = x_107;
x_10 = lean_box(0);
goto block_14;
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_trace_profiler_output;
x_6 = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_PersistentArray_isEmpty___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
x_13 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(x_10, x_9, x_12, x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_36; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_44);
lean_dec(x_14);
x_45 = lean_mk_empty_array_with_capacity(x_43);
lean_dec(x_43);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_11, x_46);
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_36 = x_45;
goto block_42;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
if (x_47 == 0)
{
lean_dec_ref(x_44);
x_36 = x_45;
goto block_42;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_46);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(x_44, x_49, x_50, x_45);
lean_dec_ref(x_44);
x_36 = x_51;
goto block_42;
}
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(x_44, x_52, x_53, x_45);
lean_dec_ref(x_44);
x_36 = x_54;
goto block_42;
}
}
block_23:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_15);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(x_10, x_15, x_17, x_18, x_16, x_1, x_2);
lean_dec_ref(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
else
{
return x_19;
}
}
block_29:
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(x_24, x_25, x_27);
lean_dec(x_27);
x_15 = x_28;
goto block_23;
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_33, x_30);
if (x_34 == 0)
{
lean_dec(x_30);
lean_inc(x_33);
x_24 = x_31;
x_25 = x_33;
x_26 = x_32;
x_27 = x_33;
goto block_29;
}
else
{
x_24 = x_31;
x_25 = x_33;
x_26 = x_32;
x_27 = x_30;
goto block_29;
}
}
block_42:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_eq(x_37, x_11);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_37, x_39);
x_41 = lean_nat_dec_le(x_11, x_40);
if (x_41 == 0)
{
lean_inc(x_40);
x_30 = x_40;
x_31 = x_36;
x_32 = x_37;
x_33 = x_40;
goto block_35;
}
else
{
x_30 = x_40;
x_31 = x_36;
x_32 = x_37;
x_33 = x_11;
goto block_35;
}
}
else
{
x_15 = x_36;
goto block_23;
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_9);
lean_dec_ref(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_7, 0, x_58);
return x_7;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
lean_dec(x_7);
x_60 = l_Lean_PersistentArray_isEmpty___redArg(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1;
x_63 = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(x_60, x_59, x_62, x_1, x_2);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_85; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_92 = lean_ctor_get(x_64, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_93);
lean_dec(x_64);
x_94 = lean_mk_empty_array_with_capacity(x_92);
lean_dec(x_92);
x_95 = lean_array_get_size(x_93);
x_96 = lean_nat_dec_lt(x_61, x_95);
if (x_96 == 0)
{
lean_dec_ref(x_93);
x_85 = x_94;
goto block_91;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_95, x_95);
if (x_97 == 0)
{
if (x_96 == 0)
{
lean_dec_ref(x_93);
x_85 = x_94;
goto block_91;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_95);
x_100 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(x_93, x_98, x_99, x_94);
lean_dec_ref(x_93);
x_85 = x_100;
goto block_91;
}
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_usize_of_nat(x_95);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(x_93, x_101, x_102, x_94);
lean_dec_ref(x_93);
x_85 = x_103;
goto block_91;
}
}
block_72:
{
lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_array_size(x_65);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(x_60, x_65, x_67, x_68, x_66, x_1, x_2);
lean_dec_ref(x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_70 = x_69;
} else {
 lean_dec_ref(x_69);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_66);
return x_71;
}
else
{
return x_69;
}
}
block_78:
{
lean_object* x_77; 
lean_dec(x_75);
x_77 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(x_73, x_74, x_76);
lean_dec(x_76);
x_65 = x_77;
goto block_72;
}
block_84:
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_82, x_79);
if (x_83 == 0)
{
lean_dec(x_79);
lean_inc(x_82);
x_73 = x_80;
x_74 = x_82;
x_75 = x_81;
x_76 = x_82;
goto block_78;
}
else
{
x_73 = x_80;
x_74 = x_82;
x_75 = x_81;
x_76 = x_79;
goto block_78;
}
}
block_91:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_eq(x_86, x_61);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_86, x_88);
x_90 = lean_nat_dec_le(x_61, x_89);
if (x_90 == 0)
{
lean_inc(x_89);
x_79 = x_89;
x_80 = x_85;
x_81 = x_86;
x_82 = x_89;
goto block_84;
}
else
{
x_79 = x_89;
x_80 = x_85;
x_81 = x_86;
x_82 = x_61;
goto block_84;
}
}
else
{
x_65 = x_85;
goto block_72;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_63, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_105 = x_63;
} else {
 lean_dec_ref(x_63);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_59);
lean_dec_ref(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_6);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_6, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_111);
return x_6;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = lean_st_ref_get(x_6);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_replaceRef(x_3, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_13);
x_14 = l_Lean_PersistentArray_toArray___redArg(x_12);
lean_dec_ref(x_12);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21(x_15, x_16, x_14);
x_18 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_18, x_5, x_6);
lean_dec_ref(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_st_ref_take(x_6);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_21);
x_28 = l_Lean_PersistentArray_push___redArg(x_1, x_27);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_22);
x_30 = lean_box(0);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get_uint64(x_24, sizeof(void*)*1);
lean_dec(x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_21);
x_33 = l_Lean_PersistentArray_push___redArg(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint64(x_34, sizeof(void*)*1, x_31);
lean_ctor_set(x_22, 4, x_34);
x_35 = lean_st_ref_set(x_6, x_22);
x_36 = lean_box(0);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_37 = lean_ctor_get(x_22, 4);
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 5);
x_43 = lean_ctor_get(x_22, 6);
x_44 = lean_ctor_get(x_22, 7);
x_45 = lean_ctor_get(x_22, 8);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_37);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_46 = lean_ctor_get_uint64(x_37, sizeof(void*)*1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_21);
x_49 = l_Lean_PersistentArray_push___redArg(x_1, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 8);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_46);
x_51 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_42);
lean_ctor_set(x_51, 6, x_43);
lean_ctor_set(x_51, 7, x_44);
lean_ctor_set(x_51, 8, x_45);
x_52 = lean_st_ref_set(x_6, x_51);
x_53 = lean_box(0);
lean_ctor_set(x_19, 0, x_53);
return x_19;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
lean_dec(x_19);
x_55 = lean_st_ref_take(x_6);
x_56 = lean_ctor_get(x_55, 4);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_55, 3);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_55, 6);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_55, 7);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_55, 8);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 lean_ctor_release(x_55, 8);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get_uint64(x_56, sizeof(void*)*1);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_54);
x_69 = l_Lean_PersistentArray_push___redArg(x_1, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 1, 8);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 9, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_58);
lean_ctor_set(x_71, 2, x_59);
lean_ctor_set(x_71, 3, x_60);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_61);
lean_ctor_set(x_71, 6, x_62);
lean_ctor_set(x_71, 7, x_63);
lean_ctor_set(x_71, 8, x_64);
x_72 = lean_st_ref_set(x_6, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_75 = lean_ctor_get(x_5, 0);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 2);
x_78 = lean_ctor_get(x_5, 3);
x_79 = lean_ctor_get(x_5, 4);
x_80 = lean_ctor_get(x_5, 5);
x_81 = lean_ctor_get(x_5, 6);
x_82 = lean_ctor_get(x_5, 7);
x_83 = lean_ctor_get(x_5, 8);
x_84 = lean_ctor_get(x_5, 9);
x_85 = lean_ctor_get(x_5, 10);
x_86 = lean_ctor_get(x_5, 11);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*14);
x_88 = lean_ctor_get(x_5, 12);
x_89 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_90 = lean_ctor_get(x_5, 13);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_5);
x_91 = lean_st_ref_get(x_6);
x_92 = lean_ctor_get(x_91, 4);
lean_inc_ref(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
lean_dec_ref(x_92);
x_94 = l_Lean_replaceRef(x_3, x_80);
lean_dec(x_80);
x_95 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_95, 0, x_75);
lean_ctor_set(x_95, 1, x_76);
lean_ctor_set(x_95, 2, x_77);
lean_ctor_set(x_95, 3, x_78);
lean_ctor_set(x_95, 4, x_79);
lean_ctor_set(x_95, 5, x_94);
lean_ctor_set(x_95, 6, x_81);
lean_ctor_set(x_95, 7, x_82);
lean_ctor_set(x_95, 8, x_83);
lean_ctor_set(x_95, 9, x_84);
lean_ctor_set(x_95, 10, x_85);
lean_ctor_set(x_95, 11, x_86);
lean_ctor_set(x_95, 12, x_88);
lean_ctor_set(x_95, 13, x_90);
lean_ctor_set_uint8(x_95, sizeof(void*)*14, x_87);
lean_ctor_set_uint8(x_95, sizeof(void*)*14 + 1, x_89);
x_96 = l_Lean_PersistentArray_toArray___redArg(x_93);
lean_dec_ref(x_93);
x_97 = lean_array_size(x_96);
x_98 = 0;
x_99 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13_spec__21(x_97, x_98, x_96);
x_100 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_4);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_100, x_95, x_6);
lean_dec_ref(x_95);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_st_ref_take(x_6);
x_105 = lean_ctor_get(x_104, 4);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 2);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_104, 3);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_104, 5);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_104, 6);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_104, 7);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_104, 8);
lean_inc_ref(x_113);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 lean_ctor_release(x_104, 5);
 lean_ctor_release(x_104, 6);
 lean_ctor_release(x_104, 7);
 lean_ctor_release(x_104, 8);
 x_114 = x_104;
} else {
 lean_dec_ref(x_104);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get_uint64(x_105, sizeof(void*)*1);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_116 = x_105;
} else {
 lean_dec_ref(x_105);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_3);
lean_ctor_set(x_117, 1, x_102);
x_118 = l_Lean_PersistentArray_push___redArg(x_1, x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 1, 8);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_uint64(x_119, sizeof(void*)*1, x_115);
if (lean_is_scalar(x_114)) {
 x_120 = lean_alloc_ctor(0, 9, 0);
} else {
 x_120 = x_114;
}
lean_ctor_set(x_120, 0, x_106);
lean_ctor_set(x_120, 1, x_107);
lean_ctor_set(x_120, 2, x_108);
lean_ctor_set(x_120, 3, x_109);
lean_ctor_set(x_120, 4, x_119);
lean_ctor_set(x_120, 5, x_110);
lean_ctor_set(x_120, 6, x_111);
lean_ctor_set(x_120, 7, x_112);
lean_ctor_set(x_120, 8, x_113);
x_121 = lean_st_ref_set(x_6, x_120);
x_122 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_103;
}
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_44; double x_77; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Lean_trace_profiler;
x_29 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_4, x_28);
if (x_29 == 0)
{
x_44 = x_29;
goto block_76;
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_trace_profiler_useHeartbeats;
x_84 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_4, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; double x_87; double x_88; double x_89; 
x_85 = l_Lean_trace_profiler_threshold;
x_86 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_4, x_85);
x_87 = lean_float_of_nat(x_86);
x_88 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__2;
x_89 = lean_float_div(x_87, x_88);
x_77 = x_89;
goto block_82;
}
else
{
lean_object* x_90; lean_object* x_91; double x_92; 
x_90 = l_Lean_trace_profiler_threshold;
x_91 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_4, x_90);
x_92 = lean_float_of_nat(x_91);
x_77 = x_92;
goto block_82;
}
}
block_25:
{
lean_object* x_20; 
x_20 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__13(x_6, x_16, x_14, x_15, x_17, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_12);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
block_38:
{
double x_33; lean_object* x_34; 
x_33 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
lean_inc_ref(x_3);
lean_inc(x_1);
x_34 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set_float(x_34, sizeof(void*)*2, x_33);
lean_ctor_set_float(x_34, sizeof(void*)*2 + 8, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 16, x_2);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_3);
lean_dec(x_1);
x_14 = x_30;
x_15 = x_31;
x_16 = x_34;
x_17 = x_9;
x_18 = x_10;
x_19 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_35; double x_36; double x_37; 
lean_dec_ref(x_34);
x_35 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_3);
x_36 = lean_unbox_float(x_26);
lean_dec(x_26);
lean_ctor_set_float(x_35, sizeof(void*)*2, x_36);
x_37 = lean_unbox_float(x_27);
lean_dec(x_27);
lean_ctor_set_float(x_35, sizeof(void*)*2 + 8, x_37);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 16, x_2);
x_14 = x_30;
x_15 = x_31;
x_16 = x_35;
x_17 = x_9;
x_18 = x_10;
x_19 = lean_box(0);
goto block_25;
}
}
block_43:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_9, 5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_12);
x_40 = lean_apply_4(x_7, x_12, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_39);
x_30 = x_39;
x_31 = x_41;
x_32 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_42; 
lean_dec_ref(x_40);
x_42 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1;
lean_inc(x_39);
x_30 = x_39;
x_31 = x_42;
x_32 = lean_box(0);
goto block_38;
}
}
block_76:
{
if (x_5 == 0)
{
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_45 = lean_st_ref_take(x_10);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_PersistentArray_append___redArg(x_6, x_49);
lean_dec_ref(x_49);
lean_ctor_set(x_47, 0, x_50);
x_51 = lean_st_ref_set(x_10, x_45);
lean_dec(x_10);
x_52 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_12);
return x_52;
}
else
{
uint64_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get_uint64(x_47, sizeof(void*)*1);
x_54 = lean_ctor_get(x_47, 0);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_PersistentArray_append___redArg(x_6, x_54);
lean_dec_ref(x_54);
x_56 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint64(x_56, sizeof(void*)*1, x_53);
lean_ctor_set(x_45, 4, x_56);
x_57 = lean_st_ref_set(x_10, x_45);
lean_dec(x_10);
x_58 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_12);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_59 = lean_ctor_get(x_45, 4);
x_60 = lean_ctor_get(x_45, 0);
x_61 = lean_ctor_get(x_45, 1);
x_62 = lean_ctor_get(x_45, 2);
x_63 = lean_ctor_get(x_45, 3);
x_64 = lean_ctor_get(x_45, 5);
x_65 = lean_ctor_get(x_45, 6);
x_66 = lean_ctor_get(x_45, 7);
x_67 = lean_ctor_get(x_45, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_59);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_45);
x_68 = lean_ctor_get_uint64(x_59, sizeof(void*)*1);
x_69 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
x_71 = l_Lean_PersistentArray_append___redArg(x_6, x_69);
lean_dec_ref(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_63);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_64);
lean_ctor_set(x_73, 6, x_65);
lean_ctor_set(x_73, 7, x_66);
lean_ctor_set(x_73, 8, x_67);
x_74 = lean_st_ref_set(x_10, x_73);
lean_dec(x_10);
x_75 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_12);
return x_75;
}
}
else
{
goto block_43;
}
}
else
{
goto block_43;
}
}
block_82:
{
double x_78; double x_79; double x_80; uint8_t x_81; 
x_78 = lean_unbox_float(x_27);
x_79 = lean_unbox_float(x_26);
x_80 = lean_float_sub(x_78, x_79);
x_81 = lean_float_decLt(x_77, x_80);
x_44 = x_81;
goto block_76;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_5);
x_14 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_1, x_12, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
return x_14;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_2 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
static double _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_18; lean_object* x_19; lean_object* x_32; uint64_t x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_io_get_tid();
x_36 = lean_st_ref_take(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_38 = lean_ctor_get(x_36, 6);
x_39 = lean_ctor_get(x_36, 8);
lean_dec(x_39);
x_40 = lean_ctor_get(x_36, 7);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 4);
lean_dec(x_41);
x_42 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_43 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint64(x_43, sizeof(void*)*1, x_35);
x_44 = l_Lean_MessageLog_markAllReported(x_38);
x_45 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
x_46 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_ctor_set(x_36, 8, x_46);
lean_ctor_set(x_36, 7, x_45);
lean_ctor_set(x_36, 6, x_44);
lean_ctor_set(x_36, 4, x_43);
x_47 = lean_st_ref_set(x_5, x_36);
x_48 = lean_ctor_get(x_4, 2);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_3);
lean_inc(x_5);
lean_inc_ref(x_4);
x_50 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
x_32 = x_50;
goto block_34;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_107; 
x_51 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_52 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_51, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_107 = lean_unbox(x_53);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = l_Lean_trace_profiler;
x_109 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_48, x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_53);
lean_dec_ref(x_3);
lean_inc(x_5);
lean_inc_ref(x_4);
x_110 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
x_32 = x_110;
goto block_34;
}
else
{
goto block_106;
}
}
else
{
goto block_106;
}
block_71:
{
lean_object* x_59; double x_60; double x_61; double x_62; double x_63; double x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_59 = lean_io_mono_nanos_now();
x_60 = lean_float_of_nat(x_56);
x_61 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
x_62 = lean_float_div(x_60, x_61);
x_63 = lean_float_of_nat(x_59);
x_64 = lean_float_div(x_63, x_61);
x_65 = lean_box_float(x_62);
x_66 = lean_box_float(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_unbox(x_53);
lean_dec(x_53);
lean_inc(x_5);
lean_inc_ref(x_4);
x_70 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_51, x_49, x_54, x_48, x_69, x_55, x_3, x_68, x_4, x_5);
x_32 = x_70;
goto block_34;
}
block_85:
{
lean_object* x_76; double x_77; double x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_76 = lean_io_get_num_heartbeats();
x_77 = lean_float_of_nat(x_72);
x_78 = lean_float_of_nat(x_76);
x_79 = lean_box_float(x_77);
x_80 = lean_box_float(x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_unbox(x_53);
lean_dec(x_53);
lean_inc(x_5);
lean_inc_ref(x_4);
x_84 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_51, x_49, x_54, x_48, x_83, x_73, x_3, x_82, x_4, x_5);
x_32 = x_84;
goto block_34;
}
block_106:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_5);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_trace_profiler_useHeartbeats;
x_89 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_48, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_io_mono_nanos_now();
lean_inc(x_5);
lean_inc_ref(x_4);
x_91 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_ctor_set_tag(x_91, 1);
x_55 = x_87;
x_56 = x_90;
x_57 = x_91;
x_58 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_55 = x_87;
x_56 = x_90;
x_57 = x_94;
x_58 = lean_box(0);
goto block_71;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
lean_ctor_set_tag(x_91, 0);
x_55 = x_87;
x_56 = x_90;
x_57 = x_91;
x_58 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_55 = x_87;
x_56 = x_90;
x_57 = x_97;
x_58 = lean_box(0);
goto block_71;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_io_get_num_heartbeats();
lean_inc(x_5);
lean_inc_ref(x_4);
x_99 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 1);
x_72 = x_98;
x_73 = x_87;
x_74 = x_99;
x_75 = lean_box(0);
goto block_85;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_72 = x_98;
x_73 = x_87;
x_74 = x_102;
x_75 = lean_box(0);
goto block_85;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_99);
if (x_103 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_72 = x_98;
x_73 = x_87;
x_74 = x_99;
x_75 = lean_box(0);
goto block_85;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_72 = x_98;
x_73 = x_87;
x_74 = x_105;
x_75 = lean_box(0);
goto block_85;
}
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_111 = lean_ctor_get(x_36, 0);
x_112 = lean_ctor_get(x_36, 1);
x_113 = lean_ctor_get(x_36, 2);
x_114 = lean_ctor_get(x_36, 3);
x_115 = lean_ctor_get(x_36, 5);
x_116 = lean_ctor_get(x_36, 6);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_36);
x_117 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_118 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set_uint64(x_118, sizeof(void*)*1, x_35);
x_119 = l_Lean_MessageLog_markAllReported(x_116);
x_120 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2;
x_121 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_122 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_112);
lean_ctor_set(x_122, 2, x_113);
lean_ctor_set(x_122, 3, x_114);
lean_ctor_set(x_122, 4, x_118);
lean_ctor_set(x_122, 5, x_115);
lean_ctor_set(x_122, 6, x_119);
lean_ctor_set(x_122, 7, x_120);
lean_ctor_set(x_122, 8, x_121);
x_123 = lean_st_ref_set(x_5, x_122);
x_124 = lean_ctor_get(x_4, 2);
x_125 = lean_ctor_get_uint8(x_124, sizeof(void*)*1);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec_ref(x_3);
lean_inc(x_5);
lean_inc_ref(x_4);
x_126 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
x_32 = x_126;
goto block_34;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_183; 
x_127 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_128 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_127, x_4);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_183 = lean_unbox(x_129);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_trace_profiler;
x_185 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_124, x_184);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_129);
lean_dec_ref(x_3);
lean_inc(x_5);
lean_inc_ref(x_4);
x_186 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
x_32 = x_186;
goto block_34;
}
else
{
goto block_182;
}
}
else
{
goto block_182;
}
block_147:
{
lean_object* x_135; double x_136; double x_137; double x_138; double x_139; double x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_135 = lean_io_mono_nanos_now();
x_136 = lean_float_of_nat(x_132);
x_137 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
x_138 = lean_float_div(x_136, x_137);
x_139 = lean_float_of_nat(x_135);
x_140 = lean_float_div(x_139, x_137);
x_141 = lean_box_float(x_138);
x_142 = lean_box_float(x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_unbox(x_129);
lean_dec(x_129);
lean_inc(x_5);
lean_inc_ref(x_4);
x_146 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_127, x_125, x_130, x_124, x_145, x_131, x_3, x_144, x_4, x_5);
x_32 = x_146;
goto block_34;
}
block_161:
{
lean_object* x_152; double x_153; double x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_152 = lean_io_get_num_heartbeats();
x_153 = lean_float_of_nat(x_148);
x_154 = lean_float_of_nat(x_152);
x_155 = lean_box_float(x_153);
x_156 = lean_box_float(x_154);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_unbox(x_129);
lean_dec(x_129);
lean_inc(x_5);
lean_inc_ref(x_4);
x_160 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_127, x_125, x_130, x_124, x_159, x_149, x_3, x_158, x_4, x_5);
x_32 = x_160;
goto block_34;
}
block_182:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_5);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = l_Lean_trace_profiler_useHeartbeats;
x_165 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_124, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_io_mono_nanos_now();
lean_inc(x_5);
lean_inc_ref(x_4);
x_167 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
 lean_ctor_set_tag(x_170, 1);
}
lean_ctor_set(x_170, 0, x_168);
x_131 = x_163;
x_132 = x_166;
x_133 = x_170;
x_134 = lean_box(0);
goto block_147;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 0);
}
lean_ctor_set(x_173, 0, x_171);
x_131 = x_163;
x_132 = x_166;
x_133 = x_173;
x_134 = lean_box(0);
goto block_147;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_io_get_num_heartbeats();
lean_inc(x_5);
lean_inc_ref(x_4);
x_175 = lean_apply_4(x_1, x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_176);
x_148 = x_174;
x_149 = x_163;
x_150 = x_178;
x_151 = lean_box(0);
goto block_161;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_180;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_179);
x_148 = x_174;
x_149 = x_163;
x_150 = x_181;
x_151 = lean_box(0);
goto block_161;
}
}
}
}
}
block_17:
{
lean_object* x_8; 
x_8 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_st_ref_get(x_5);
lean_dec(x_5);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_st_ref_get(x_5);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
block_31:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Exception_toMessageData(x_18);
lean_inc_ref(x_4);
x_22 = l_Lean_logError___at___00Lean_Core_wrapAsyncAsSnapshot_spec__1(x_21, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_7 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_23);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
lean_dec_ref(x_18);
x_7 = lean_box(0);
goto block_17;
}
}
block_34:
{
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
x_7 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_33;
x_19 = lean_box(0);
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_get_set_stdin(x_1);
lean_dec_ref(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_get_set_stdin(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_ctor_set_tag(x_8, 1);
x_11 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(x_6, x_7, x_8);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(x_6, x_7, x_16);
lean_dec_ref(x_16);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_18 = x_17;
} else {
 lean_dec_ref(x_17);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___lam__0(x_6, x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_get_set_stdout(x_1);
lean_dec_ref(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_get_set_stdout(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_ctor_set_tag(x_8, 1);
x_11 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(x_6, x_7, x_8);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(x_6, x_7, x_16);
lean_dec_ref(x_16);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_18 = x_17;
} else {
 lean_dec_ref(x_17);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___lam__0(x_6, x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_get_set_stderr(x_1);
lean_dec_ref(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_get_set_stderr(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_ctor_set_tag(x_8, 1);
x_11 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(x_6, x_7, x_8);
lean_dec_ref(x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(x_6, x_7, x_16);
lean_dec_ref(x_16);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_18 = x_17;
} else {
 lean_dec_ref(x_17);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___lam__0(x_6, x_7, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_ByteArray_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__3));
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(193u);
x_4 = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__2));
x_5 = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0;
x_13 = lean_st_mk_ref(x_12);
x_14 = lean_st_mk_ref(x_12);
x_15 = l_IO_FS_Stream_ofBuffer(x_13);
lean_inc(x_14);
x_16 = l_IO_FS_Stream_ofBuffer(x_14);
if (x_2 == 0)
{
x_17 = x_1;
goto block_30;
}
else
{
lean_object* x_31; 
lean_inc_ref(x_16);
x_31 = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__19___boxed), 6, 3);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_16);
lean_closure_set(x_31, 2, x_1);
x_17 = x_31;
goto block_30;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_30:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__16___boxed), 6, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
x_19 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg(x_15, x_18, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_string_validate_utf8(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_22);
x_24 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4;
x_25 = l_panic___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__18(x_24);
x_6 = x_20;
x_7 = lean_box(0);
x_8 = x_25;
goto block_11;
}
else
{
lean_object* x_26; 
x_26 = lean_string_from_utf8_unchecked(x_22);
x_6 = x_20;
x_7 = lean_box(0);
x_8 = x_26;
goto block_11;
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___boxed), 6, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_2);
x_9 = l_Lean_Core_stderrAsMessages;
x_10 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_7, x_9);
x_11 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg(x_8, x_10, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
x_2 = l_Lean_Language_instInhabitedSnapshotLeaf_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_4, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Core_mkSnapshot_x3f(x_8, x_2, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0;
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = l_Lean_Language_instInhabitedSnapshotTree_default;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2___boxed), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_inc_ref(x_4);
x_9 = l_Lean_Core_wrapAsync___redArg(x_8, x_2, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___boxed), 5, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_3);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___boxed), 5, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4_spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_6);
x_15 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4(x_1, x_2, x_13, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5_spec__17(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__8___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__11_spec__23(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2_spec__7_spec__16_spec__24___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_28; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 11);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
x_20 = lean_ctor_get(x_4, 12);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*14 + 1);
x_22 = lean_ctor_get(x_4, 13);
lean_inc_ref(x_22);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 lean_ctor_release(x_4, 13);
 x_23 = x_4;
} else {
 lean_dec_ref(x_4);
 x_23 = lean_box(0);
}
x_28 = lean_nat_dec_le(x_1, x_11);
if (x_28 == 0)
{
lean_dec(x_11);
x_24 = x_1;
goto block_27;
}
else
{
lean_dec(x_1);
x_24 = x_11;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 14, 2);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_12);
lean_ctor_set(x_25, 6, x_13);
lean_ctor_set(x_25, 7, x_14);
lean_ctor_set(x_25, 8, x_15);
lean_ctor_set(x_25, 9, x_16);
lean_ctor_set(x_25, 10, x_17);
lean_ctor_set(x_25, 11, x_18);
lean_ctor_set(x_25, 12, x_20);
lean_ctor_set(x_25, 13, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*14, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*14 + 1, x_21);
x_26 = lean_apply_3(x_3, x_25, x_5, lean_box(0));
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_3(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_instBEqInternalExceptionId_beq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_2(x_1, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalId___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_3(x_6, lean_box(0), x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_3(x_9, lean_box(0), x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_List_elem___redArg(x_2, x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_2(x_1, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_apply_1(x_4, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l_Lean_catchInternalIds___redArg___closed__0));
x_8 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_3(x_6, lean_box(0), x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = ((lean_object*)(l_Lean_catchInternalIds___redArg___closed__0));
x_11 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_7);
x_12 = lean_apply_3(x_9, lean_box(0), x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_MessageData_stripNestedTags(x_2);
x_4 = l_Lean_MessageData_kind(x_3);
lean_dec_ref(x_3);
x_5 = ((lean_object*)(l_Lean_Core_throwMaxHeartbeat___redArg___closed__1));
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec_ref(x_1);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_mkArrow___closed__1));
x_7 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = 0;
x_11 = l_Lean_mkForall(x_9, x_10, x_1, x_2);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 0;
x_14 = l_Lean_mkForall(x_12, x_13, x_1, x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrow(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 1;
x_10 = lean_usize_sub(x_2, x_9);
x_11 = lean_array_uget(x_1, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_mkArrow(x_11, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_6);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkArrowN_spec__0(x_1, x_10, x_11, x_2, x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrowN(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__2));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__4));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__7));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__8));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__10));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__12));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__13));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__14));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__16));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__17));
x_2 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_12; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
lean_inc(x_4);
lean_inc_ref(x_2);
x_14 = l_Lean_isAuxRecursor(x_2, x_4);
if (x_14 == 0)
{
x_12 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
lean_inc(x_4);
lean_inc_ref(x_2);
x_15 = l_Lean_isCasesOnRecursor(x_2, x_4);
if (x_15 == 0)
{
x_12 = x_14;
goto block_13;
}
else
{
goto block_11;
}
}
block_9:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_6 = l_Array_contains___redArg(x_1, x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
block_11:
{
uint8_t x_10; 
lean_inc(x_4);
x_10 = l_Lean_isRecCore(x_2, x_4);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_10;
}
else
{
goto block_9;
}
}
block_13:
{
if (x_12 == 0)
{
goto block_11;
}
else
{
lean_dec_ref(x_2);
goto block_9;
}
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = 0;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_10; 
x_10 = lean_find_expr(x_2, x_6);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1;
x_14 = 0;
x_15 = l_Lean_MessageData_ofConstName(x_12, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___redArg(x_3, x_4, x_18);
return x_19;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
goto block_9;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_inc_ref(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed), 6, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___redArg(x_3, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___closed__0));
x_10 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2), 6, 5);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_traceBlock_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_io_wait(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceBlock___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_traceBlock___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_io_get_task_state(x_2);
if (x_6 == 2)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_task_get_own(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_11 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_11, 0, x_2);
if (x_10 == 0)
{
lean_dec_ref(x_1);
x_12 = x_3;
x_13 = x_9;
x_14 = x_4;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_80; 
x_20 = ((lean_object*)(l_Lean_traceBlock___redArg___closed__2));
x_21 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_20, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_23, 0, x_1);
x_80 = lean_unbox(x_22);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_trace_profiler;
x_82 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_9, x_81);
if (x_82 == 0)
{
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_1);
x_12 = x_3;
x_13 = x_9;
x_14 = x_4;
x_15 = lean_box(0);
goto block_19;
}
else
{
goto block_79;
}
}
else
{
goto block_79;
}
block_37:
{
lean_object* x_28; double x_29; double x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_28 = lean_io_get_num_heartbeats();
x_29 = lean_float_of_nat(x_24);
x_30 = lean_float_of_nat(x_28);
x_31 = lean_box_float(x_29);
x_32 = lean_box_float(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unbox(x_22);
lean_dec(x_22);
x_36 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_20, x_10, x_1, x_9, x_35, x_25, x_23, x_34, x_3, x_4);
lean_dec_ref(x_9);
return x_36;
}
block_54:
{
lean_object* x_42; double x_43; double x_44; double x_45; double x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_42 = lean_io_mono_nanos_now();
x_43 = lean_float_of_nat(x_38);
x_44 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3;
x_45 = lean_float_div(x_43, x_44);
x_46 = lean_float_of_nat(x_42);
x_47 = lean_float_div(x_46, x_44);
x_48 = lean_box_float(x_45);
x_49 = lean_box_float(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_unbox(x_22);
lean_dec(x_22);
x_53 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg(x_20, x_10, x_1, x_9, x_52, x_39, x_23, x_51, x_3, x_4);
lean_dec_ref(x_9);
return x_53;
}
block_79:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg(x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_trace_profiler_useHeartbeats;
x_58 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_9, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_io_mono_nanos_now();
x_60 = ((lean_object*)(l_Lean_traceBlock___redArg___closed__0));
x_61 = lean_box(0);
lean_inc(x_4);
lean_inc_ref(x_3);
x_62 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(x_60, x_9, x_11, x_61, x_3, x_4);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 1);
x_38 = x_59;
x_39 = x_56;
x_40 = x_62;
x_41 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_38 = x_59;
x_39 = x_56;
x_40 = x_65;
x_41 = lean_box(0);
goto block_54;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_ctor_set_tag(x_62, 0);
x_38 = x_59;
x_39 = x_56;
x_40 = x_62;
x_41 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_38 = x_59;
x_39 = x_56;
x_40 = x_68;
x_41 = lean_box(0);
goto block_54;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_io_get_num_heartbeats();
x_70 = ((lean_object*)(l_Lean_traceBlock___redArg___closed__0));
x_71 = lean_box(0);
lean_inc(x_4);
lean_inc_ref(x_3);
x_72 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(x_70, x_9, x_11, x_71, x_3, x_4);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 1);
x_24 = x_69;
x_25 = x_56;
x_26 = x_72;
x_27 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_24 = x_69;
x_25 = x_56;
x_26 = x_75;
x_27 = lean_box(0);
goto block_37;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_ctor_set_tag(x_72, 0);
x_24 = x_69;
x_25 = x_56;
x_26 = x_72;
x_27 = lean_box(0);
goto block_37;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_24 = x_69;
x_25 = x_56;
x_26 = x_78;
x_27 = lean_box(0);
goto block_37;
}
}
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = ((lean_object*)(l_Lean_traceBlock___redArg___closed__0));
x_17 = lean_box(0);
x_18 = l_Lean_profileitM___at___00Lean_traceBlock_spec__0___redArg(x_16, x_13, x_11, x_17, x_12, x_14);
lean_dec_ref(x_13);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_traceBlock___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_traceBlock___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_traceBlock(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPostponedCompileDecl_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
if (x_4 == 0)
{
if (x_6 == 0)
{
return x_7;
}
else
{
return x_4;
}
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPostponedCompileDecl_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqPostponedCompileDecl_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashablePostponedCompileDecl_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = 0;
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
if (x_3 == 0)
{
uint64_t x_7; uint64_t x_8; 
x_7 = 13;
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
else
{
uint64_t x_9; uint64_t x_10; 
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePostponedCompileDecl_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashablePostponedCompileDecl_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn___lam__1_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_initFn___lam__3_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__8_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_;
x_6 = l_Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_));
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_compileDeclsRef;
x_6 = lean_st_ref_get(x_5);
x_7 = lean_apply_4(x_6, x_1, x_2, x_3, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDeclsImpl(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Core_saveState___redArg(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_inc(x_4);
x_8 = l_Lean_compileDeclsImpl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Core_SavedState_restore___redArg(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
if (x_2 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_dec(x_10);
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = lean_name_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_4, x_2);
lean_dec_ref(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg(x_5, x_2);
return x_7;
}
else
{
lean_dec_ref(x_5);
return x_6;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_8, x_2);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_6;
}
}
}
else
{
uint8_t x_12; 
lean_dec_ref(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 5);
lean_dec(x_9);
x_10 = l_Lean_Environment_setExporting(x_8, x_2);
lean_ctor_set(x_6, 5, x_3);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_ctor_get(x_6, 6);
x_20 = lean_ctor_get(x_6, 7);
x_21 = lean_ctor_get(x_6, 8);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_22 = l_Lean_Environment_setExporting(x_14, x_2);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_3);
lean_ctor_set(x_23, 6, x_19);
lean_ctor_set(x_23, 7, x_20);
lean_ctor_set(x_23, 8, x_21);
x_24 = lean_st_ref_set(x_1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_take(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 5);
lean_dec(x_12);
x_13 = l_Lean_Environment_setExporting(x_11, x_2);
x_14 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_9, 5, x_14);
lean_ctor_set(x_9, 0, x_13);
x_15 = lean_st_ref_set(x_4, x_9);
lean_inc(x_4);
x_16 = lean_apply_3(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_ctor_set_tag(x_16, 1);
x_19 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_4, x_8, x_14, x_16);
lean_dec_ref(x_16);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_4, x_8, x_14, x_24);
lean_dec_ref(x_24);
lean_dec(x_4);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_26 = x_25;
} else {
 lean_dec_ref(x_25);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_23);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec_ref(x_16);
x_29 = lean_box(0);
x_30 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_4, x_8, x_14, x_29);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 4);
x_39 = lean_ctor_get(x_9, 6);
x_40 = lean_ctor_get(x_9, 7);
x_41 = lean_ctor_get(x_9, 8);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_42 = l_Lean_Environment_setExporting(x_34, x_2);
x_43 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_43);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_40);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_st_ref_set(x_4, x_44);
lean_inc(x_4);
x_46 = lean_apply_3(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_47);
x_50 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_4, x_8, x_43, x_49);
lean_dec_ref(x_49);
lean_dec(x_4);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_51 = x_50;
} else {
 lean_dec_ref(x_50);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_47);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec_ref(x_46);
x_54 = lean_box(0);
x_55 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___lam__0(x_4, x_8, x_43, x_54);
lean_dec(x_4);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_56 = x_55;
} else {
 lean_dec_ref(x_55);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_53);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, lean_box(0));
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg(x_1, x_7, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_box(x_2);
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_12 = 1;
x_13 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(x_8, x_12, x_3, x_4);
return x_13;
}
else
{
if (x_11 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_14 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(x_8, x_11, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_15);
lean_dec(x_6);
x_16 = l_Lean_Environment_constants(x_15);
x_17 = 0;
x_18 = lean_usize_of_nat(x_10);
x_19 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__2(x_16, x_1, x_17, x_18);
lean_dec_ref(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(x_8, x_11, x_3, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_compileDecls_doCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lean_CoreM_0__Lean_compileDecls_doCompile(x_1, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0_spec__0(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lean_withoutExporting___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__0(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__2_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00__private_Lean_CoreM_0__Lean_compileDecls_doCompile_spec__1_spec__3_spec__5_spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 5);
lean_dec(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_4, 5, x_8);
lean_ctor_set(x_4, 0, x_1);
x_9 = lean_st_ref_set(x_2, x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 6);
x_17 = lean_ctor_get(x_4, 7);
x_18 = lean_ctor_get(x_4, 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_19 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_20 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set(x_20, 6, x_16);
lean_ctor_set(x_20, 7, x_17);
lean_ctor_set(x_20, 8, x_18);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_compileDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_2, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecls___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(x_1, x_7);
lean_dec_ref(x_9);
lean_inc(x_7);
x_10 = l___private_Lean_CoreM_0__Lean_compileDecls_doCompile(x_3, x_4, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_ctor_set_tag(x_10, 1);
x_13 = l_Lean_compileDecls___lam__0(x_7, x_2, x_10);
lean_dec_ref(x_10);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_compileDecls___lam__0(x_7, x_2, x_18);
lean_dec_ref(x_18);
lean_dec(x_7);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_20 = x_19;
} else {
 lean_dec_ref(x_19);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = lean_box(0);
x_24 = l_Lean_compileDecls___lam__0(x_7, x_2, x_23);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_compileDecls___lam__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_compileDecls_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_2, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_st_ref_take(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; double x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_16 = 0;
x_17 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_15);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_16);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_19);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_PersistentArray_push___redArg(x_14, x_21);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_st_ref_set(x_4, x_10);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
uint64_t x_25; lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_28 = 0;
x_29 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_PersistentArray_push___redArg(x_26, x_33);
x_35 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_25);
lean_ctor_set(x_10, 4, x_35);
x_36 = lean_st_ref_set(x_4, x_10);
x_37 = lean_box(0);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; double x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_38 = lean_ctor_get(x_10, 4);
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
x_41 = lean_ctor_get(x_10, 2);
x_42 = lean_ctor_get(x_10, 3);
x_43 = lean_ctor_get(x_10, 5);
x_44 = lean_ctor_get(x_10, 6);
x_45 = lean_ctor_get(x_10, 7);
x_46 = lean_ctor_get(x_10, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_47 = lean_ctor_get_uint64(x_38, sizeof(void*)*1);
x_48 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
x_50 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_51 = 0;
x_52 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_51);
x_54 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_55 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_PersistentArray_push___redArg(x_48, x_56);
if (lean_is_scalar(x_49)) {
 x_58 = lean_alloc_ctor(0, 1, 8);
} else {
 x_58 = x_49;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint64(x_58, sizeof(void*)*1, x_47);
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_41);
lean_ctor_set(x_59, 3, x_42);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_43);
lean_ctor_set(x_59, 6, x_44);
lean_ctor_set(x_59, 7, x_45);
lean_ctor_set(x_59, 8, x_46);
x_60 = lean_st_ref_set(x_4, x_59);
x_61 = lean_box(0);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; double x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_st_ref_take(x_4);
x_64 = lean_ctor_get(x_63, 4);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_63, 5);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_63, 6);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_63, 7);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_63, 8);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 lean_ctor_release(x_63, 7);
 lean_ctor_release(x_63, 8);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get_uint64(x_64, sizeof(void*)*1);
x_75 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
x_77 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0;
x_78 = 0;
x_79 = ((lean_object*)(l_Lean_useDiagnosticMsg___lam__2___closed__2));
x_80 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_float(x_80, sizeof(void*)*2, x_77);
lean_ctor_set_float(x_80, sizeof(void*)*2 + 8, x_77);
lean_ctor_set_uint8(x_80, sizeof(void*)*2 + 16, x_78);
x_81 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0;
x_82 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set(x_82, 2, x_81);
lean_inc(x_6);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_PersistentArray_push___redArg(x_75, x_83);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 1, 8);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint64(x_85, sizeof(void*)*1, x_74);
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 9, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_66);
lean_ctor_set(x_86, 2, x_67);
lean_ctor_set(x_86, 3, x_68);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_69);
lean_ctor_set(x_86, 6, x_70);
lean_ctor_set(x_86, 7, x_71);
lean_ctor_set(x_86, 8, x_72);
x_87 = lean_st_ref_set(x_4, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_compileDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lean_compileDecls_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__2));
x_12 = l_Lean_isTracingEnabledFor___at___00Lean_Core_wrapAsyncAsSnapshot_spec__2___redArg(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_54; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_array_uget(x_2, x_4);
x_54 = lean_unbox(x_13);
lean_dec(x_13);
if (x_54 == 0)
{
x_16 = x_7;
x_17 = lean_box(0);
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4;
lean_inc(x_15);
x_56 = l_Lean_MessageData_ofName(x_15);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___00Lean_compileDecls_spec__1(x_11, x_57, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_16 = x_7;
x_17 = lean_box(0);
goto block_53;
}
else
{
lean_dec(x_15);
return x_58;
}
}
block_53:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_st_ref_take(x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 5);
lean_dec(x_21);
x_22 = l_Lean_postponedCompileDeclsExt;
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_1);
x_26 = lean_box(0);
x_27 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_22, x_20, x_25, x_24, x_26);
lean_dec(x_24);
x_28 = l_Lean_Core_instInhabitedCache_default___closed__2;
lean_ctor_set(x_18, 5, x_28);
lean_ctor_set(x_18, 0, x_27);
x_29 = lean_st_ref_set(x_16, x_18);
x_30 = 1;
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 2);
x_36 = lean_ctor_get(x_18, 3);
x_37 = lean_ctor_get(x_18, 4);
x_38 = lean_ctor_get(x_18, 6);
x_39 = lean_ctor_get(x_18, 7);
x_40 = lean_ctor_get(x_18, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_41 = l_Lean_postponedCompileDeclsExt;
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_1);
x_45 = lean_box(0);
x_46 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_41, x_33, x_44, x_43, x_45);
lean_dec(x_43);
x_47 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
lean_ctor_set(x_48, 4, x_37);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_48, 6, x_38);
lean_ctor_set(x_48, 7, x_39);
lean_ctor_set(x_48, 8, x_40);
x_49 = lean_st_ref_set(x_16, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_4, x_50);
x_4 = x_51;
x_5 = x_14;
goto _start;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_12);
if (x_59 == 0)
{
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2(x_9, x_2, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_7 = l_Lean_isMarkedMeta(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_7;
}
}
else
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_73; 
x_73 = lean_st_ref_get(x_5);
if (x_3 == 0)
{
lean_dec(x_73);
x_7 = x_4;
x_8 = x_5;
x_9 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
lean_dec(x_73);
x_75 = l_Lean_Environment_header(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*7 + 4);
lean_dec_ref(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_74);
x_7 = x_4;
x_8 = x_5;
x_9 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; 
x_77 = lean_box(0);
x_78 = lean_array_size(x_1);
x_79 = 0;
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2(x_2, x_1, x_78, x_79, x_77, x_4, x_5);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec_ref(x_80);
x_81 = l_Lean_compiler_postponeCompile;
x_82 = l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg(x_81, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_array_get_size(x_1);
x_90 = lean_nat_dec_lt(x_88, x_89);
if (x_90 == 0)
{
lean_dec_ref(x_74);
goto block_87;
}
else
{
if (x_90 == 0)
{
lean_dec_ref(x_74);
goto block_87;
}
else
{
size_t x_91; uint8_t x_92; 
x_91 = lean_usize_of_nat(x_89);
x_92 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_compileDecls_spec__4(x_74, x_1, x_79, x_91);
if (x_92 == 0)
{
goto block_87;
}
else
{
lean_dec(x_84);
lean_dec(x_83);
x_7 = x_4;
x_8 = x_5;
x_9 = lean_box(0);
goto block_72;
}
}
}
block_87:
{
uint8_t x_85; 
x_85 = lean_unbox(x_83);
lean_dec(x_83);
if (x_85 == 0)
{
lean_dec(x_84);
x_7 = x_4;
x_8 = x_5;
x_9 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_86; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_77);
return x_86;
}
}
}
else
{
lean_dec_ref(x_74);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_80;
}
}
}
block_72:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = l_Lean_Elab_async;
x_12 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_st_ref_get(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_Lean_compileDecls___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = l_Lean_traceBlock___redArg(x_16, x_15, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l___private_Lean_CoreM_0__Lean_compileDecls_doCompile(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
return x_18;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_st_ref_get(x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec(x_27);
lean_inc_ref(x_28);
x_29 = l_Lean_Environment_promiseChecked(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(x_30, x_8);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_IO_CancelToken_new();
x_36 = lean_box(x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_compileDecls___lam__1___boxed), 8, 4);
lean_closure_set(x_37, 0, x_31);
lean_closure_set(x_37, 1, x_29);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_36);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_35);
x_38 = ((lean_object*)(l_Lean_compileDecls___closed__2));
x_39 = l_Lean_Name_toString(x_38, x_12);
lean_inc_ref(x_32);
x_40 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_37, x_32, x_39, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_42);
lean_dec_ref(x_28);
x_43 = 0;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_io_map_task(x_41, x_42, x_44, x_43);
x_46 = lean_box(0);
x_47 = lean_box(2);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_32);
lean_ctor_set(x_48, 3, x_45);
x_49 = l_Lean_Core_logSnapshotTask___redArg(x_48, x_8);
lean_dec(x_8);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec_ref(x_32);
lean_dec_ref(x_28);
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
lean_dec(x_40);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_53 = l_IO_CancelToken_new();
x_54 = lean_box(x_2);
x_55 = lean_alloc_closure((void*)(l_Lean_compileDecls___lam__1___boxed), 8, 4);
lean_closure_set(x_55, 0, x_31);
lean_closure_set(x_55, 1, x_29);
lean_closure_set(x_55, 2, x_1);
lean_closure_set(x_55, 3, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_57 = ((lean_object*)(l_Lean_compileDecls___closed__2));
x_58 = l_Lean_Name_toString(x_57, x_12);
lean_inc_ref(x_56);
x_59 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_55, x_56, x_58, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_61);
lean_dec_ref(x_28);
x_62 = 0;
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_io_map_task(x_60, x_61, x_63, x_62);
x_65 = lean_box(0);
x_66 = lean_box(2);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_56);
lean_ctor_set(x_67, 3, x_64);
x_68 = l_Lean_Core_logSnapshotTask___redArg(x_67, x_8);
lean_dec(x_8);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_56);
lean_dec_ref(x_28);
lean_dec(x_8);
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_compileDecls(x_1, x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_compileDecls_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_getM___at___00Lean_compileDecls_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_getDeclNamesForCodeGen(x_1);
x_8 = l_Lean_compileDecls(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_compileDecl(x_1, x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_diagnostics;
x_3 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getDiag(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*14);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_isDiagnosticsEnabled___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__6() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2;
x_2 = l_Lean_Core_instInhabitedCache_default___closed__1;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Options_empty;
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_ImportM_runCoreM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_diagnostics;
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ImportM_runCoreM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_maxRecDepth;
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_171; uint8_t x_190; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Core_instInhabitedCache_default___closed__2;
x_6 = l_Lean_ImportM_runCoreM___redArg___closed__0;
x_7 = lean_io_get_num_heartbeats();
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_firstFrontendMacroScope;
x_11 = l_Lean_ImportM_runCoreM___redArg___closed__1;
x_12 = ((lean_object*)(l_Lean_ImportM_runCoreM___redArg___closed__4));
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = ((lean_object*)(l_Lean_ImportM_runCoreM___redArg___closed__5));
x_16 = l_Lean_ImportM_runCoreM___redArg___closed__6;
x_17 = l_Lean_ImportM_runCoreM___redArg___closed__7;
x_18 = l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0;
lean_inc_ref(x_8);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_5);
lean_ctor_set(x_19, 6, x_6);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_mk_ref(x_19);
x_111 = l_Lean_inheritedTraceOptions;
x_112 = lean_st_ref_get(x_111);
x_113 = lean_st_ref_get(x_20);
x_114 = ((lean_object*)(l_Lean_ImportM_runCoreM___redArg___closed__8));
x_115 = l_Lean_instInhabitedFileMap_default;
x_116 = l_Lean_Options_empty;
x_117 = lean_unsigned_to_nat(1000u);
x_118 = lean_box(0);
x_119 = l_Lean_ImportM_runCoreM___redArg___closed__9;
x_120 = 0;
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_115);
lean_ctor_set(x_122, 2, x_116);
lean_ctor_set(x_122, 3, x_4);
lean_ctor_set(x_122, 4, x_117);
lean_ctor_set(x_122, 5, x_118);
lean_ctor_set(x_122, 6, x_13);
lean_ctor_set(x_122, 7, x_14);
lean_ctor_set(x_122, 8, x_7);
lean_ctor_set(x_122, 9, x_119);
lean_ctor_set(x_122, 10, x_13);
lean_ctor_set(x_122, 11, x_10);
lean_ctor_set(x_122, 12, x_121);
lean_ctor_set(x_122, 13, x_112);
lean_ctor_set_uint8(x_122, sizeof(void*)*14, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*14 + 1, x_120);
x_123 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_123);
lean_dec(x_113);
x_124 = l_Lean_diagnostics;
x_125 = l_Lean_ImportM_runCoreM___redArg___closed__10;
x_190 = l_Lean_Kernel_isDiagnosticsEnabled(x_123);
lean_dec_ref(x_123);
if (x_190 == 0)
{
if (x_125 == 0)
{
lean_inc(x_20);
x_126 = x_122;
x_127 = x_20;
x_128 = lean_box(0);
goto block_170;
}
else
{
x_171 = x_190;
goto block_189;
}
}
else
{
x_171 = x_125;
goto block_189;
}
block_67:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_Option_get___at___00Lean_Core_getMaxHeartbeats_spec__0(x_9, x_22);
lean_dec_ref(x_22);
lean_inc_ref(x_9);
x_39 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_9);
lean_ctor_set(x_39, 3, x_25);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_26);
lean_ctor_set(x_39, 6, x_27);
lean_ctor_set(x_39, 7, x_28);
lean_ctor_set(x_39, 8, x_29);
lean_ctor_set(x_39, 9, x_30);
lean_ctor_set(x_39, 10, x_31);
lean_ctor_set(x_39, 11, x_32);
lean_ctor_set(x_39, 12, x_33);
lean_ctor_set(x_39, 13, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*14, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*14 + 1, x_34);
x_40 = lean_apply_3(x_1, x_39, x_36, lean_box(0));
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_st_ref_get(x_20);
lean_dec(x_20);
lean_dec(x_42);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_st_ref_get(x_20);
lean_dec(x_20);
lean_dec(x_44);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_MessageData_toString(x_48);
x_50 = lean_mk_io_user_error(x_49);
lean_ctor_set(x_40, 0, x_50);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec_ref(x_47);
x_52 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_53 = l_Nat_reprFast(x_51);
x_54 = lean_string_append(x_52, x_53);
lean_dec_ref(x_53);
x_55 = lean_mk_io_user_error(x_54);
lean_ctor_set(x_40, 0, x_55);
return x_40;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_40, 0);
lean_inc(x_56);
lean_dec(x_40);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_MessageData_toString(x_57);
x_59 = lean_mk_io_user_error(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec_ref(x_56);
x_62 = ((lean_object*)(l_Lean_Core_CoreM_toIO___redArg___closed__0));
x_63 = l_Nat_reprFast(x_61);
x_64 = lean_string_append(x_62, x_63);
lean_dec_ref(x_63);
x_65 = lean_mk_io_user_error(x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
}
block_86:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_70, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 9);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 10);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 11);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 12);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_70, sizeof(void*)*14 + 1);
x_85 = lean_ctor_get(x_70, 13);
lean_inc_ref(x_85);
lean_dec_ref(x_70);
x_21 = x_68;
x_22 = x_69;
x_23 = x_73;
x_24 = x_74;
x_25 = x_75;
x_26 = x_76;
x_27 = x_77;
x_28 = x_78;
x_29 = x_79;
x_30 = x_80;
x_31 = x_81;
x_32 = x_82;
x_33 = x_83;
x_34 = x_84;
x_35 = x_85;
x_36 = x_71;
x_37 = lean_box(0);
goto block_67;
}
block_110:
{
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_st_ref_take(x_91);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 5);
lean_dec(x_96);
x_97 = l_Lean_Kernel_enableDiag(x_95, x_88);
lean_ctor_set(x_93, 5, x_5);
lean_ctor_set(x_93, 0, x_97);
x_98 = lean_st_ref_set(x_91, x_93);
x_68 = x_88;
x_69 = x_89;
x_70 = x_90;
x_71 = x_91;
x_72 = lean_box(0);
goto block_86;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_93, 0);
x_100 = lean_ctor_get(x_93, 1);
x_101 = lean_ctor_get(x_93, 2);
x_102 = lean_ctor_get(x_93, 3);
x_103 = lean_ctor_get(x_93, 4);
x_104 = lean_ctor_get(x_93, 6);
x_105 = lean_ctor_get(x_93, 7);
x_106 = lean_ctor_get(x_93, 8);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_93);
x_107 = l_Lean_Kernel_enableDiag(x_99, x_88);
x_108 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
lean_ctor_set(x_108, 2, x_101);
lean_ctor_set(x_108, 3, x_102);
lean_ctor_set(x_108, 4, x_103);
lean_ctor_set(x_108, 5, x_5);
lean_ctor_set(x_108, 6, x_104);
lean_ctor_set(x_108, 7, x_105);
lean_ctor_set(x_108, 8, x_106);
x_109 = lean_st_ref_set(x_91, x_108);
x_68 = x_88;
x_69 = x_89;
x_70 = x_90;
x_71 = x_91;
x_72 = lean_box(0);
goto block_86;
}
}
else
{
x_68 = x_88;
x_69 = x_89;
x_70 = x_90;
x_71 = x_91;
x_72 = lean_box(0);
goto block_86;
}
}
block_170:
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_st_ref_get(x_127);
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
x_133 = lean_ctor_get(x_126, 3);
x_134 = lean_ctor_get(x_126, 5);
x_135 = lean_ctor_get(x_126, 6);
x_136 = lean_ctor_get(x_126, 7);
x_137 = lean_ctor_get(x_126, 8);
x_138 = lean_ctor_get(x_126, 9);
x_139 = lean_ctor_get(x_126, 10);
x_140 = lean_ctor_get(x_126, 11);
x_141 = lean_ctor_get(x_126, 12);
x_142 = lean_ctor_get_uint8(x_126, sizeof(void*)*14 + 1);
x_143 = lean_ctor_get(x_126, 13);
x_144 = lean_ctor_get(x_126, 4);
lean_dec(x_144);
x_145 = lean_ctor_get(x_126, 2);
lean_dec(x_145);
x_146 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_146);
lean_dec(x_129);
x_147 = l_Lean_maxRecDepth;
x_148 = l_Lean_ImportM_runCoreM___redArg___closed__11;
lean_inc_ref(x_143);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc_ref(x_132);
lean_inc_ref(x_131);
lean_ctor_set(x_126, 4, x_148);
lean_ctor_set(x_126, 2, x_116);
lean_ctor_set_uint8(x_126, sizeof(void*)*14, x_125);
x_149 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_9, x_124);
x_150 = l_Lean_Kernel_isDiagnosticsEnabled(x_146);
lean_dec_ref(x_146);
if (x_150 == 0)
{
if (x_149 == 0)
{
lean_dec_ref(x_126);
x_21 = x_149;
x_22 = x_147;
x_23 = x_131;
x_24 = x_132;
x_25 = x_133;
x_26 = x_134;
x_27 = x_135;
x_28 = x_136;
x_29 = x_137;
x_30 = x_138;
x_31 = x_139;
x_32 = x_140;
x_33 = x_141;
x_34 = x_142;
x_35 = x_143;
x_36 = x_127;
x_37 = lean_box(0);
goto block_67;
}
else
{
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
x_87 = lean_box(0);
x_88 = x_149;
x_89 = x_147;
x_90 = x_126;
x_91 = x_127;
x_92 = x_150;
goto block_110;
}
}
else
{
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
x_87 = lean_box(0);
x_88 = x_149;
x_89 = x_147;
x_90 = x_126;
x_91 = x_127;
x_92 = x_149;
goto block_110;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; 
x_151 = lean_ctor_get(x_126, 0);
x_152 = lean_ctor_get(x_126, 1);
x_153 = lean_ctor_get(x_126, 3);
x_154 = lean_ctor_get(x_126, 5);
x_155 = lean_ctor_get(x_126, 6);
x_156 = lean_ctor_get(x_126, 7);
x_157 = lean_ctor_get(x_126, 8);
x_158 = lean_ctor_get(x_126, 9);
x_159 = lean_ctor_get(x_126, 10);
x_160 = lean_ctor_get(x_126, 11);
x_161 = lean_ctor_get(x_126, 12);
x_162 = lean_ctor_get_uint8(x_126, sizeof(void*)*14 + 1);
x_163 = lean_ctor_get(x_126, 13);
lean_inc(x_163);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_126);
x_164 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_164);
lean_dec(x_129);
x_165 = l_Lean_maxRecDepth;
x_166 = l_Lean_ImportM_runCoreM___redArg___closed__11;
lean_inc_ref(x_163);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc_ref(x_152);
lean_inc_ref(x_151);
x_167 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_152);
lean_ctor_set(x_167, 2, x_116);
lean_ctor_set(x_167, 3, x_153);
lean_ctor_set(x_167, 4, x_166);
lean_ctor_set(x_167, 5, x_154);
lean_ctor_set(x_167, 6, x_155);
lean_ctor_set(x_167, 7, x_156);
lean_ctor_set(x_167, 8, x_157);
lean_ctor_set(x_167, 9, x_158);
lean_ctor_set(x_167, 10, x_159);
lean_ctor_set(x_167, 11, x_160);
lean_ctor_set(x_167, 12, x_161);
lean_ctor_set(x_167, 13, x_163);
lean_ctor_set_uint8(x_167, sizeof(void*)*14, x_125);
lean_ctor_set_uint8(x_167, sizeof(void*)*14 + 1, x_162);
x_168 = l_Lean_Option_get___at___00Lean_useDiagnosticMsg_spec__0(x_9, x_124);
x_169 = l_Lean_Kernel_isDiagnosticsEnabled(x_164);
lean_dec_ref(x_164);
if (x_169 == 0)
{
if (x_168 == 0)
{
lean_dec_ref(x_167);
x_21 = x_168;
x_22 = x_165;
x_23 = x_151;
x_24 = x_152;
x_25 = x_153;
x_26 = x_154;
x_27 = x_155;
x_28 = x_156;
x_29 = x_157;
x_30 = x_158;
x_31 = x_159;
x_32 = x_160;
x_33 = x_161;
x_34 = x_162;
x_35 = x_163;
x_36 = x_127;
x_37 = lean_box(0);
goto block_67;
}
else
{
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
x_87 = lean_box(0);
x_88 = x_168;
x_89 = x_165;
x_90 = x_167;
x_91 = x_127;
x_92 = x_169;
goto block_110;
}
}
else
{
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
x_87 = lean_box(0);
x_88 = x_168;
x_89 = x_165;
x_90 = x_167;
x_91 = x_127;
x_92 = x_168;
goto block_110;
}
}
}
block_189:
{
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_st_ref_take(x_20);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 5);
lean_dec(x_175);
x_176 = l_Lean_Kernel_enableDiag(x_174, x_125);
lean_ctor_set(x_172, 5, x_5);
lean_ctor_set(x_172, 0, x_176);
x_177 = lean_st_ref_set(x_20, x_172);
lean_inc(x_20);
x_126 = x_122;
x_127 = x_20;
x_128 = lean_box(0);
goto block_170;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
x_180 = lean_ctor_get(x_172, 2);
x_181 = lean_ctor_get(x_172, 3);
x_182 = lean_ctor_get(x_172, 4);
x_183 = lean_ctor_get(x_172, 6);
x_184 = lean_ctor_get(x_172, 7);
x_185 = lean_ctor_get(x_172, 8);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_172);
x_186 = l_Lean_Kernel_enableDiag(x_178, x_125);
x_187 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_181);
lean_ctor_set(x_187, 4, x_182);
lean_ctor_set(x_187, 5, x_5);
lean_ctor_set(x_187, 6, x_183);
lean_ctor_set(x_187, 7, x_184);
lean_ctor_set(x_187, 8, x_185);
x_188 = lean_st_ref_set(x_20, x_187);
lean_inc(x_20);
x_126 = x_122;
x_127 = x_20;
x_128 = lean_box(0);
goto block_170;
}
}
else
{
lean_inc(x_20);
x_126 = x_122;
x_127 = x_20;
x_128 = lean_box(0);
goto block_170;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ImportM_runCoreM___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Exception_isMaxRecDepth(x_1);
return x_3;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isRuntime(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_11 = l_Lean_Exception_isInterrupt(x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_7);
x_12 = l_Lean_Exception_isRuntime(x_7);
x_8 = x_12;
goto block_10;
}
else
{
x_8 = x_11;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
x_9 = lean_apply_4(x_2, x_7, x_3, x_4, lean_box(0));
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_tryCatch___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_12 = l_Lean_Exception_isInterrupt(x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_8);
x_13 = l_Lean_Exception_isRuntime(x_8);
x_9 = x_13;
goto block_11;
}
else
{
x_9 = x_12;
goto block_11;
}
block_11:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
x_10 = lean_apply_4(x_3, x_8, x_4, x_5, lean_box(0));
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_tryCatch(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_Exception_isInterrupt(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
x_9 = lean_apply_4(x_2, x_7, x_3, x_4, lean_box(0));
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_tryCatchRuntimeEx___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_Exception_isInterrupt(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
x_10 = lean_apply_4(x_3, x_8, x_4, x_5, lean_box(0));
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_tryCatchRuntimeEx(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadExceptOfExceptionCoreM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, lean_box(0), x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mapCoreM___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
x_10 = lean_apply_1(x_7, lean_box(0));
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
x_12 = lean_apply_1(x_9, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_NameSet_contains(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 2);
x_13 = l_Lean_NameSet_insert(x_12, x_1);
lean_ctor_set(x_10, 2, x_13);
x_14 = lean_st_ref_set(x_2, x_8);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_21 = l_Lean_NameSet_insert(x_20, x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_8, 6, x_22);
x_23 = lean_st_ref_set(x_2, x_8);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_8, 6);
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 4);
x_33 = lean_ctor_get(x_8, 5);
x_34 = lean_ctor_get(x_8, 7);
x_35 = lean_ctor_get(x_8, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_27);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_36 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_27, 2);
lean_inc(x_38);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_39 = x_27;
} else {
 lean_dec_ref(x_27);
 x_39 = lean_box(0);
}
x_40 = l_Lean_NameSet_insert(x_38, x_1);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 3, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set(x_42, 4, x_32);
lean_ctor_set(x_42, 5, x_33);
lean_ctor_set(x_42, 6, x_41);
lean_ctor_set(x_42, 7, x_34);
lean_ctor_set(x_42, 8, x_35);
x_43 = lean_st_ref_set(x_2, x_42);
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_logMessageKind___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_Environment_enableRealizationsForConst(x_6, x_7, x_1);
x_9 = l_Lean_setEnv___at___00Lean_compileDecls_spec__0___redArg(x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_enableRealizationsForConst(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_CoreM_0__Lean_initFn___closed__7_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l_Lean_traceBlock___redArg___closed__2));
x_7 = l_Lean_registerTraceClass(x_6, x_3, x_4);
return x_7;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin);
lean_object* initialize_Lean_ResolveName(uint8_t builtin);
lean_object* initialize_Lean_Language_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_CoreM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_RecDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_3719377344____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_1504562188____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics_threshold);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_1276945831____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxHeartbeats);
lean_dec_ref(res);
}l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_2159144449____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_async = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_async);
lean_dec_ref(res);
}l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_4053927728____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_inServer = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_inServer);
lean_dec_ref(res);
}l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_652821380____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_internal_cmdlineSnapshots = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internal_cmdlineSnapshots);
lean_dec_ref(res);
}l_Lean_useDiagnosticMsg___lam__0___closed__2 = _init_l_Lean_useDiagnosticMsg___lam__0___closed__2();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__0___closed__2);
l_Lean_useDiagnosticMsg___lam__2___closed__4 = _init_l_Lean_useDiagnosticMsg___lam__2___closed__4();
lean_mark_persistent(l_Lean_useDiagnosticMsg___lam__2___closed__4);
l_Lean_useDiagnosticMsg___closed__3 = _init_l_Lean_useDiagnosticMsg___closed__3();
lean_mark_persistent(l_Lean_useDiagnosticMsg___closed__3);
l_Lean_useDiagnosticMsg = _init_l_Lean_useDiagnosticMsg();
lean_mark_persistent(l_Lean_useDiagnosticMsg);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__17_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__19_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__21_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_);
l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_ = _init_l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_Core_initFn___closed__22_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_CoreM_0__Lean_Core_initFn_00___x40_Lean_CoreM_3777671385____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Core_instInhabitedCache_default___closed__0 = _init_l_Lean_Core_instInhabitedCache_default___closed__0();
lean_mark_persistent(l_Lean_Core_instInhabitedCache_default___closed__0);
l_Lean_Core_instInhabitedCache_default___closed__1 = _init_l_Lean_Core_instInhabitedCache_default___closed__1();
lean_mark_persistent(l_Lean_Core_instInhabitedCache_default___closed__1);
l_Lean_Core_instInhabitedCache_default___closed__2 = _init_l_Lean_Core_instInhabitedCache_default___closed__2();
lean_mark_persistent(l_Lean_Core_instInhabitedCache_default___closed__2);
l_Lean_Core_instInhabitedCache_default = _init_l_Lean_Core_instInhabitedCache_default();
lean_mark_persistent(l_Lean_Core_instInhabitedCache_default);
l_Lean_Core_instInhabitedCache = _init_l_Lean_Core_instInhabitedCache();
lean_mark_persistent(l_Lean_Core_instInhabitedCache);
l_Lean_Core_instMonadCoreM___closed__0 = _init_l_Lean_Core_instMonadCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__0);
l_Lean_Core_instMonadCoreM___closed__1 = _init_l_Lean_Core_instMonadCoreM___closed__1();
lean_mark_persistent(l_Lean_Core_instMonadCoreM___closed__1);
l_Lean_Core_instMonadCoreM = _init_l_Lean_Core_instMonadCoreM();
lean_mark_persistent(l_Lean_Core_instMonadCoreM);
l_Lean_Core_instInhabitedCoreM___lam__0___closed__0 = _init_l_Lean_Core_instInhabitedCoreM___lam__0___closed__0();
lean_mark_persistent(l_Lean_Core_instInhabitedCoreM___lam__0___closed__0);
l_Lean_Core_instMonadWithOptionsCoreM___closed__0 = _init_l_Lean_Core_instMonadWithOptionsCoreM___closed__0();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM___closed__0);
l_Lean_Core_instMonadWithOptionsCoreM = _init_l_Lean_Core_instMonadWithOptionsCoreM();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM);
l_Lean_Core_instAddMessageContextCoreM = _init_l_Lean_Core_instAddMessageContextCoreM();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM);
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Core_instantiateTypeLevelParams_spec__1_spec__2___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Core_instantiateTypeLevelParams_spec__0_spec__0___redArg___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_instantiateValueLevelParams_spec__0_spec__0___closed__6);
l_Lean_Core_instantiateValueLevelParams___closed__1 = _init_l_Lean_Core_instantiateValueLevelParams___closed__1();
lean_mark_persistent(l_Lean_Core_instantiateValueLevelParams___closed__1);
l_Lean_Core_withIncRecDepth___redArg___closed__0 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__0);
l_Lean_Core_withIncRecDepth___redArg___closed__1 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__1();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__1);
l_Lean_Core_withIncRecDepth___redArg___closed__2 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__2();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__2);
l_Lean_Core_withIncRecDepth___redArg___closed__3 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__3);
l_Lean_Core_withIncRecDepth___redArg___closed__4 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__4();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__4);
l_Lean_Core_withIncRecDepth___redArg___closed__5 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__5();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__5);
l_Lean_Core_withIncRecDepth___redArg___closed__6 = _init_l_Lean_Core_withIncRecDepth___redArg___closed__6();
lean_mark_persistent(l_Lean_Core_withIncRecDepth___redArg___closed__6);
l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_ = _init_l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Core_initFn___closed__4_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Core_initFn_00___x40_Lean_CoreM_2405441116____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_debug_moduleNameAtTimeout = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_debug_moduleNameAtTimeout);
lean_dec_ref(res);
}l_Lean_Core_throwMaxHeartbeat___redArg___closed__3 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__3);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__5 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__5();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__5);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__7 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__7();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__7);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__9 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__9();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__9);
l_Lean_Core_throwMaxHeartbeat___redArg___closed__11 = _init_l_Lean_Core_throwMaxHeartbeat___redArg___closed__11();
lean_mark_persistent(l_Lean_Core_throwMaxHeartbeat___redArg___closed__11);
l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0 = _init_l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwInterruptException___at___00Lean_Core_checkSystem_spec__0___redArg___closed__0);
l_Lean_Core_resetMessageLog___redArg___closed__0 = _init_l_Lean_Core_resetMessageLog___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__0);
l_Lean_Core_resetMessageLog___redArg___closed__1 = _init_l_Lean_Core_resetMessageLog___redArg___closed__1();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__1);
l_Lean_Core_resetMessageLog___redArg___closed__2 = _init_l_Lean_Core_resetMessageLog___redArg___closed__2();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__2);
l_Lean_Core_resetMessageLog___redArg___closed__3 = _init_l_Lean_Core_resetMessageLog___redArg___closed__3();
lean_mark_persistent(l_Lean_Core_resetMessageLog___redArg___closed__3);
l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0 = _init_l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0();
lean_mark_persistent(l_Lean_Core_getAndEmptySnapshotTasks___redArg___closed__0);
l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_ = _init_l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Core_initFn___closed__3_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Core_initFn_00___x40_Lean_CoreM_768847207____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_stderrAsMessages);
lean_dec_ref(res);
}l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__3);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__10);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__11);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__18);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__19);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__20);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__21);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__23);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__24);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__26);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__27);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__29);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__30);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__31);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__32);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__33);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__34);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__35);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__36);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__37);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__38);
l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1___closed__39);
l_Lean_Core_mkSnapshot_x3f___auto__1 = _init_l_Lean_Core_mkSnapshot_x3f___auto__1();
lean_mark_persistent(l_Lean_Core_mkSnapshot_x3f___auto__1);
l_Lean_Core_wrapAsyncAsSnapshot___auto__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___auto__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___auto__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Core_wrapAsyncAsSnapshot_spec__3___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3_spec__10_spec__21_spec__29___redArg___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___closed__0();
l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0 = _init_l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__0);
l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1 = _init_l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1();
lean_mark_persistent(l_Lean_addTraceAsMessages___at___00Lean_Core_wrapAsyncAsSnapshot_spec__0___closed__1);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Core_wrapAsyncAsSnapshot_spec__4___redArg___closed__2();
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__0);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__1);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__2);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1___closed__3();
l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___00Lean_Core_wrapAsyncAsSnapshot_spec__5___redArg___closed__4);
l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0 = _init_l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3___closed__0);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__18);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__19);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__20);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__21);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__22);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__23);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__24);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__25);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__26);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__27);
l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28 = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors___closed__28);
l___private_Lean_CoreM_0__Lean_supportedRecursors = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__1);
l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3 = _init_l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___closed__3);
l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_3543162477____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_compiler_postponeCompile = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_compiler_postponeCompile);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_685484229____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_postponedCompileDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_postponedCompileDeclsExt);
lean_dec_ref(res);
}l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_CoreM_2504870994____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_compileDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_compileDeclsRef);
lean_dec_ref(res);
}l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_compileDecls_spec__2___closed__4);
l_Lean_ImportM_runCoreM___redArg___closed__0 = _init_l_Lean_ImportM_runCoreM___redArg___closed__0();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__0);
l_Lean_ImportM_runCoreM___redArg___closed__1 = _init_l_Lean_ImportM_runCoreM___redArg___closed__1();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__1);
l_Lean_ImportM_runCoreM___redArg___closed__6 = _init_l_Lean_ImportM_runCoreM___redArg___closed__6();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__6);
l_Lean_ImportM_runCoreM___redArg___closed__7 = _init_l_Lean_ImportM_runCoreM___redArg___closed__7();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__7);
l_Lean_ImportM_runCoreM___redArg___closed__9 = _init_l_Lean_ImportM_runCoreM___redArg___closed__9();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__9);
l_Lean_ImportM_runCoreM___redArg___closed__10 = _init_l_Lean_ImportM_runCoreM___redArg___closed__10();
l_Lean_ImportM_runCoreM___redArg___closed__11 = _init_l_Lean_ImportM_runCoreM___redArg___closed__11();
lean_mark_persistent(l_Lean_ImportM_runCoreM___redArg___closed__11);
if (builtin) {res = l___private_Lean_CoreM_0__Lean_initFn_00___x40_Lean_CoreM_660971656____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
