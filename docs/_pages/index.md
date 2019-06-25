---
layout: home
permalink: /
---

<section class="hero"><div class="wrapper">
	<h1>GREEN</h1>
	{% include svg/green.svg %}
	<h2>A Java program analysis tool built on concolic execution and fuzz testing</h2>
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
			{% include svg/clipboard.svg %}
			<h3>Reduce</h3>
			<p>
				COASTAL can generate a test suite to test software up to a desired level of coverage in situations where a complete and executable specification of correct behaviour is not available.  A test suite that covers all behaviour is useful for regression testing and when migrating from legacy to new code.
			</p>
		</div>
		<div class="gridbox3">
			{% include svg/bug.svg %}
			<h3>Reuse</h3>
			<p>
				Null pointer exceptions.
			</p>
		</div>
		<div class="gridbox3">
			{% include svg/pie-chart.svg %}
			<h3>Recycle</h3>
			<p>
				Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.
			</p>
		</div>
	</div>
</div></section>
