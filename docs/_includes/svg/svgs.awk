#===============================================================================
# Usage:
# $ gawk -f svgs.awk < svgs.txt > svgs.svg
#
# For individual pictures:
# $ gawk -v picture=share -f svgs.awk < svgs.txt > picture.svg
#
# Optional conversion to png:
# $ convert picture.svg picture.png
#===============================================================================

BEGIN {
	DEBUG = 0
	GAP = 20
	inDef = 0
	inCall = 0
	activePic = 1
	lineCount = 0
	level = 0
	height = 0
	attrs[-1]["@@"] = 1
	initGreen()
}

function trim(str) {
	return gensub(/^[[:space:]]+|[[:space:]]+$/, "", "g", str)
}

function getAttrs(s,k) {
	s = ""
	if (isarray(attrs[level])) {
		for (k in attrs[level]) {
			# if (DEBUG > 0) { print "==> attrs["level"]["k"]" }
			if (k == "@@") {
				continue
			} else if (!(k in attrs[level - 1])) {
				s = s" "sprintf("%s=\"%s\"", k, attrs[level][k])
			} else if (attrs[level - 1][k] != attrs[level][k]) {
				s = s" "sprintf("%s=\"%s\"", k, attrs[level][k])
			}
		}
	} else {
		if (DEBUG > 0) { print "==> attrs[level] is not an array" }
	}
	return s
}

function addLine(line) {
	if (activePic > 0) {
		lines[lineCount] = line
		lineCount++
	}
}

function addHeight(h) {
	height += h + GAP
}

function levelUp() {
	level++
	delete attrs[level]
	attrs[level]["@@"] = 1
	if (DEBUG) { print "==> levelUp: level -> "level }
}

function levelDown() {
	if (level > 0) {
		level--
	}
	if (DEBUG > 0) {
		print "==> levelDown: level -> "level
		if (isarray(attrs[level])) {
			for (k in attrs[level]) {
				if (DEBUG > 0) { print "==> attrs["level"]["k"]" }
			}
		}
	}
}

function g() {
	addLine(sprintf("<g%s>", getAttrs()))
	levelUp()
}

function endG() {
	addLine("</g>")
	levelDown()
}

function recollect(a,seps,n,start, s,i) {
	s = ""
	for (i = start; i < n; i++) {
		s = s""a[i]""seps[i]
	}
	return trim(s""a[n])
}

function setVar(vardef, n,q,qq,var,def) {
	n = split(vardef, q, FS, qq)
	var = trim(q[1])
	def = recollect(q, qq, n, 2)
	varDef[inCall][var] = def
	if (DEBUG > 0) { printf("==> setting variable {%s} <- {%s}\n", var, def) }
}

function replaceAll(line,old,new, i,newline) {
	if (DEBUG > 1) { printf("*** old=\"%s\" new=\"%s\"\n", old, new) }
	i = index(line, old)
	while (i > 0) {
		if (DEBUG > 1) { printf("*** i=%d line=\"%s\"\n", i, line) }
		line = substr(line, 1, i - 1)""new""substr(line, i + length(old))
		i = index(line, old)
	}
	return line
}

function replaceVars(line, var,def,prev) {
	if (DEBUG > 0) { printf("==> replaceVars: %s\n", line) }
	for (var in varDef[inCall]) {
		def = varDef[inCall][var]
		prev = line
		line = replaceAll(line, var, def)
		if (DEBUG > 0) { printf("==> replace %s/%s --> %s\n", var, def, line) }
	}
	if (DEBUG > 0) { printf("==> replaceVars result: %s\n", line) }
	return line
}

function processLine(line, q,qq,s,n,x,y,x1,y1,x2,y2,r,a,x3,y3,x4,y4,i,m,nn) {
	if (line ~ /^[ \t]*\*ENDDEF\>/) {
		if (inDef > 0) {
			inDef--
		}
	} else if (inDef == 1) {
		defLines[curDef][defLineCount[curDef]] = line
		defLineCount[curDef]++
	} else if (inDef > 0) {
		# IGNORE
	} else if (line ~ /^[ \t]*\*G\>/) {
		if (DEBUG > 0) { print "==> G" }
		g()
	} else if (line ~ /^[ \t]*\*ENDG\>/) {
		endG()
	} else if (line ~ /^[ \t]*\*PIC\>/) {
		split(line, q)
		thisPicture = q[2]
		if (picture == thisPicture) {
			activePic = 1
		} else if (picture != "") {
			activePic = 0
		}
		picWidth[thisPicture] = q[3]
		picHeight[thisPicture] = q[4]
		if (picture == "") {
			addLine(sprintf("\n\n<!-- ======================================================================== -->"))
			addLine(sprintf("<!-- %s -->", thisPicture))
			addLine(sprintf("<defs><clipPath id=\"cp_%s\"><rect x=\"0\" y=\"0\" width=\"%.3f\" height=\"%.3f\"/></clipPath></defs>", thisPicture, q[3], q[4]))
			addLine(sprintf("<g transform=\"translate(0,%d)\" clip-path=\"url(#cp_%s)\">", height, thisPicture))
		} else {
			addLine(sprintf("<defs><clipPath id=\"cp_%s\"><rect x=\"0\" y=\"0\" width=\"%.3f\" height=\"%.3f\"/></clipPath></defs>", thisPicture, q[3], q[4]))
			addLine(sprintf("<g clip-path=\"url(#cp_%s)\">", thisPicture))
		}
		addHeight(q[4])
		levelUp()
	} else if (line ~ /^[ \t]*\*ENDPIC\>/) {
		addLine(sprintf("</g><!-- %s -->", thisPicture))
		levelDown()
		activePic = 1
	} else if (line ~ /^[ \t]*\*CIRCLE\>/) {
		split(line, q)
		addLine(sprintf("<circle cx=\"%s\" cy=\"%s\" r=\"%s\"%s/>", q[2], q[3], q[4], q[5], getAttrs()))
	} else if (line ~ /^[ \t]*\*RECT\>/) {
		split(line, q)
		addLine(sprintf("<rect x=\"%s\" y=\"%s\" width=\"%s\" height=\"%s\"%s/>", q[2], q[3], q[4], q[5], getAttrs()))
	} else if (line ~ /^[ \t]*\*C_RECT\>/) {
		split(line, q)
		addLine(sprintf("<rect x=\"%s\" y=\"%s\" width=\"%s\" height=\"%s\" transform=\"translate(%.3f,%.3f)\"%s/>", q[2], q[3], q[4], q[5], -q[4]*0.5, -q[5]*0.5, getAttrs()))
	} else if (line ~ /^[ \t]*\*LINE\>/) {
		split(line, q)
		addLine(sprintf("<line x1=\"%s\" y1=\"%s\" x2=\"%s\" y2=\"%s\"%s/>", q[2], q[3], q[4], q[5], getAttrs()))
	} else if (line ~ /^[ \t]*\*POLYGON\>/) {
		n = split(line, q, FS, qq)
		s = recollect(q, qq, n, 2)
		addLine(sprintf("<polygon points=\"%s\"%s/>", s, getAttrs()))
	} else if (line ~ /^[ \t]*\*PATH\>/) {
		n = split(line, q, FS, qq)
		s = recollect(q, qq, n, 2)
		addLine(sprintf("<path d=\"%s\"%s/>", s, getAttrs()))
	} else if (line ~ /^[ \t]*\*GREEN\>/) {
		n = split(line, q)
		addLine(sprintf("<g transform=\"translate(%.3f,%.3f)scale(%.3f)translate(-180,-153)\">", q[2], q[3], q[4]))
		for (i = 0; i < greenSize; i++) {
			addLine(greenDef[i])
		}
		addLine("</g>")
	} else if (line ~ /^[ \t]*\*C_TEXT\>/) {
		n = split(line, q, FS, qq)
		x = q[2]
		y = q[3]
		s = recollect(q, qq, n, 4)
		addLine(sprintf("<text x=\"%s\" y=\"%s\" text-anchor=\"middle\" transform=\"translate(0,2.5%)\" dominant-baseline=\"central\"%s>%s</text>", x, y, getAttrs(), s))
	} else if (line ~ /^[ \t]*\*TEXT\>/) {
		n = split(line, q, FS, qq)
		x = q[2]
		y = q[3]
		s = recollect(q, qq, n, 4)
		addLine(sprintf("<text x=\"%s\" y=\"%s\"%s>%s</text>", x, y, getAttrs(), s))
	} else if (line ~ /^[ \t]*\*ARROW\>/) {
		n = split(line, q, FS, qq)
		g()
		x1 = q[2] ; y1 = q[3]
		x2 = q[4] ; y2 = q[5]
		r = q[6]
		a = atan2(y1 - y2, x1 - x2)
		x3 = x2 + r * cos(a + 0.78542)
		y3 = y2 + r * sin(a + 0.78542)
		x4 = x2 + r * cos(a - 0.78542)
		y4 = y2 + r * sin(a - 0.78542)
		addLine(sprintf("<line x1=\"%.3f\" y1=\"%.3f\" x2=\"%.3f\" y2=\"%.3f\"%s/>", x1, y1, x2, y2, getAttrs()))
		addLine(sprintf("<polyline points=\"%.3f,%.3f %.3f,%.3f %.3f,%.3f\" fill=\"none\" stroke-linecap=\"square\" stroke-linejoin=\"miter\"%s/>", x3, y3, x2, y2, x4, y4, getAttrs()))
		endG()
	} else if (line ~ /^[ \t]*\*DEF\>/) {
     	inDef++
     	if (inDef == 1) {
			n = split(line, q)
     		curDef = trim(q[2])
			defLineCount[curDef] = 0
     	}
	} else if (line ~ /^[ \t]*\*CALL\>/) {
		g()
		n = split(line, q)
		m = trim(q[2])
		n = split(line, q, " \\| ")
		inCall++
		delete vars[inCall]
		for (i = 2; i <= n; i++) {
			setVar(q[i])
		}
		if (m in defLineCount) {
			nn = defLineCount[m]
			for (i = 0; i < nn; i++) {
				processLine(replaceVars(defLines[m][i]))
			}
		}
		inCall--
		endG()
	} else {
		n = split(line, q, FS, qq)
		key = trim(q[1])
		val = recollect(q, qq, n, 2)
		attrs[level][key] = val
	}
}

function initGreen(i) {
	i = 0
	greenDef[i++] = "<g style=\"transform: translate(0,207)\">"
	greenDef[i++] = "<g style=\"stroke:none;stroke-width:0;\">"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(300,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(280,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(260,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(240,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(220,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(200,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(180,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(160,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(140,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(120,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(100,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(80,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(60,272)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(40,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(20,272)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(320,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(300,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(280,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(260,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(240,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(220,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(200,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(180,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(160,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(140,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(120,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(100,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(80,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(60,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(40,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(20,238)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(0,238)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(320,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(300,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(280,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(260,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(240,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(220,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(200,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(180,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(160,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(140,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(120,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(100,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(80,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(60,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(40,204)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(20,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(0,204)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(300,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(280,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(260,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(240,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(220,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(200,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(180,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(160,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(140,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(120,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(100,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(80,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(60,170)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(40,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(20,170)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(280,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(260,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(240,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(220,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(200,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(180,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(160,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(140,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(120,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(100,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(80,136)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(60,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(40,136)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(260,102)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(240,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(220,102)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(200,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(180,102)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(160,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(140,102)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(120,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(100,102)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(80,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(60,102)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(240,68)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(220,68)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(200,68)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(180,68)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(160,68)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(140,68)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(120,68)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#3e7bac;\" transform=\"translate(100,68)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#3b9942;\" transform=\"translate(80,68)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(220,34)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(200,34)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(180,34)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(160,34)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(140,34)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#2a6798;\" transform=\"translate(120,34)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(100,34)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#27852e;\" transform=\"translate(200,0)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(180,0)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(160,0)\" />"
	greenDef[i++] = "<polygon points=\"20,34  0,0  40,0\" style=\"fill:#9ebdd5;\" transform=\"translate(140,0)\" />"
	greenDef[i++] = "<polygon points=\"20,0  0,34  40,34\" style=\"fill:#9dcca0;\" transform=\"translate(120,0)\" />"
	greenDef[i++] = "</g>"
	greenDef[i++] = "</g>"
	greenSize = i
}

(DEBUG > 0) { print "--> "$0 }
/^[ \t]*$/ { next }
/^[ \t]*#/ { next }
/^[ \t]*\*G\>/ { processLine($0) ;next }
/^[ \t]*\*ENDG\>/ { processLine($0) ; next }
/^[ \t]*\*PIC\>/ { processLine($0) ; next }
/^[ \t]*\*ENDPIC\>/ { processLine($0) ; next }
/^[ \t]*\*CIRCLE\>/ { processLine($0) ; next }
/^[ \t]*\*RECT\>/ { processLine($0) ; next }
/^[ \t]*\*C_RECT\>/ { processLine($0) ; next }
/^[ \t]*\*LINE\>/ { processLine($0) ; next }
/^[ \t]*\*POLYGON\>/ { processLine($0) ; next }
/^[ \t]*\*PATH\>/ { processLine($0) ; next }
/^[ \t]*\*C_TEXT\>/ { processLine($0) ; next }
/^[ \t]*\*TEXT\>/ { processLine($0) ; next }
/^[ \t]*\*ARROW\>/ { processLine($0) ; next }
/^[ \t]*\*GREEN\>/ { processLine($0) ; next }
/^[ \t]*\*DEF\>/ { processLine($0) ; next }
/^[ \t]*\*ENDDEF\>/ { processLine($0) ; next }
/^[ \t]*\*CALL\>/ { processLine($0) ; next }
/^[ \t]*\*END\>/ { nextfile }
{ processLine($0) ; next }

END {
	if (picture == "") {
		printf("<?xml version=\"1.0\" ?>\n")
		printf("<!DOCTYPE svg  PUBLIC '-//W3C//DTD SVG 1.1//EN' 'http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd'>\n")
		printf("<svg height=\"%dpx\" xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" xml:space=\"preserve\">\n", height - GAP)
	} else {
		printf("<svg viewBox=\"0 0 %.3f %.3f\">\n", picWidth[picture], picHeight[picture])
	}
	for (i = 0; i < lineCount; i++) {
		printf("%s\n", lines[i])
	}
	printf("</svg>\n")
}
