---
layout: home
permalink: /
---

<section class="hero"><div class="wrapper">
	<h1>GREEN</h1>
	{% include svg/green.svg %}
	<h2>A universal interface to a range of SAT/SMT decision procedures, constraint solvers, model counters, and related tools. Queries are reduced, reused, and recycled by built-in routines for simplification and persistence.</h2>
	<div class="buttons">
		<a class="button" href="{{ '/userguide/getting-started/' | relative_url }}">Get started</a>
		<span class="github-button"><iframe src="https://ghbtns.com/github-btn.html?user=GreenSolver&amp;repo=green&amp;type=star&amp;count=true&amp;size=large" frameBorder="0" scrolling="0" width="160" height="30" title="GitHub Stars"></iframe></span>
	</div>
	<div class="clearfix"></div>
</div></section>

<section class="announcement"><div class="wrapper">
	We're working on a major overhaul of this documentation.<br/>
	Please be patient: everything should be ready by <span style="color:#ffff00;">August 2019</span>.
</div></section>

<section class="frontpage-section other"><div class="wrapper">
	<div class="gridboxes">
		<div class="gridbox3">
			{% include image.html name="factorizer" %}
			<h3>REDUCE</h3>
			<p>
				Incoming constraints are factorized into unrelated subconstraints:
				In further steps, the factors are processed independently.
			</p>
		</div>
		<div class="gridbox3">
			{% include image.html name="canonizer" %}
			<h3>REUSE</h3>
			<p>
				Constraints are "canonized" with simple rewrite rules and renaming variables.
				Even though canonization is not perfect, the quick-and-dirty normal form can boost reuse significantly.
			</p>
		</div>
		<div class="gridbox3">
			{% include image.html name="share" %}
			<h3>RECYCLE</h3>
			<p>
				Results from all steps are cached in a shared persistent store.
				This allows results from different users and tools to be re-used and shared.
				When stored results are not available an external solver is invoked.
			</p>
		</div>
	</div>
	<div class="gridboxes">
		<div class="gridbox3 other1">
			{% include image.html name="pipeline" %}
			<h3>DISTRIBUTION</h3>
			<p>
				A powerful configuration language is used to describe query pipelines.
				Execution is automatically distributed to available processing nodes.
			</p>
		</div>
		<div class="gridbox3 other2">
			{% include image.html name="store" %}
			<h3>STORES</h3>
			<p>
				The "store" can be configured as local or distributed, as private or public, and can use a variety of databases, for example organized in a hierarchy.
			</p>
		</div>
		<div class="gridbox3 other3">
			{% include image.html name="portfolio" %}
			<h3>PORTFOLIO</h3>
			<p>
				GREEN processes queries with a variety of established solvers: Choco, STP, Z3, CVC4, OpenSMT, Yices, LattE, Barvinok.
			</p>
		</div>
	</div>
</div></section>
