
#define __MAKE_MSYS2__

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tree.h"
#include "stringpool.h"
#include "diagnostic-core.h"
#include "attribs.h"
#include "stor-layout.h"
#include "langhooks.h"
#include "plugin.h"

extern struct lang_hooks lang_hooks;

struct ggc_root_tab;
extern ggc_root_tab ** gt_pch_scalar_rtab;
extern ggc_root_tab ** gt_ggc_rtab;
extern ggc_root_tab ** gt_ggc_deletable_rtab;

extern void __set__pointers(struct lang_hooks *p__lang_hooks,
			    ggc_root_tab ** p__gt_pch_scalar_rtab,
			    ggc_root_tab ** gt_ggc_rtab,
			    ggc_root_tab ** gt_ggc_deletable_rtab,
		     void (*p__apply_tm_attr) (tree, tree),
		     tree (*p__decl_attributes) (tree *, tree, int),
		     tree (*p__make_attribute) (const char *, const char *, tree),
		     const struct attribute_spec * (*p__lookup_attribute_spec) (const_tree),
		     tree (*p__get_attribute_name) (const_tree),
		     tree (*p__convert) (tree, tree),
		     void (*p__gt_pch_nx_language_function) (void *),
		     void (*p__gt_ggc_mx_language_function) (void *),
		     void (*p__gt_ggc_mx_lang_tree_node) (void *),
		     void (*p__gt_pch_nx_lang_tree_node) (void *),
		     void (*p__gt_clear_caches) ()
);

static struct __0 {
  __0() {
    __set__pointers(&lang_hooks, gt_pch_scalar_rtab, gt_ggc_rtab, gt_ggc_deletable_rtab,
		    apply_tm_attr, decl_attributes, make_attribute, lookup_attribute_spec,
		    get_attribute_name, convert, gt_pch_nx_language_function, gt_ggc_mx_language_function,
		    gt_ggc_mx_lang_tree_node, gt_pch_nx_lang_tree_node, gt_clear_caches);
  }
} ___1;
