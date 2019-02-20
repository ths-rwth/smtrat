<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:html="http://www.w3.org/TR/REC-html40"  xmlns:anim="urn:oasis:names:tc:opendocument:xmlns:animation:1.0" xmlns:chart="urn:oasis:names:tc:opendocument:xmlns:chart:1.0" xmlns:config="urn:oasis:names:tc:opendocument:xmlns:config:1.0" xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:dom="http://www.w3.org/2001/xml-events" xmlns:dr3d="urn:oasis:names:tc:opendocument:xmlns:dr3d:1.0" xmlns:draw="urn:oasis:names:tc:opendocument:xmlns:drawing:1.0" xmlns:fo="urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0" xmlns:form="urn:oasis:names:tc:opendocument:xmlns:form:1.0" xmlns:math="http://www.w3.org/1998/Math/MathML" xmlns:meta="urn:oasis:names:tc:opendocument:xmlns:meta:1.0" xmlns:number="urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0" xmlns:office="urn:oasis:names:tc:opendocument:xmlns:office:1.0" xmlns:presentation="urn:oasis:names:tc:opendocument:xmlns:presentation:1.0" xmlns:ooo="http://openoffice.org/2004/office" xmlns:oooc="http://openoffice.org/2004/calc" xmlns:ooow="http://openoffice.org/2004/writer" xmlns:script="urn:oasis:names:tc:opendocument:xmlns:script:1.0" xmlns:smil="urn:oasis:names:tc:opendocument:xmlns:smil-compatible:1.0" xmlns:style="urn:oasis:names:tc:opendocument:xmlns:style:1.0" xmlns:svg="urn:oasis:names:tc:opendocument:xmlns:svg-compatible:1.0" xmlns:table="urn:oasis:names:tc:opendocument:xmlns:table:1.0" xmlns:text="urn:oasis:names:tc:opendocument:xmlns:text:1.0" xmlns:xforms="http://www.w3.org/2002/xforms" xmlns:xlink="http://www.w3.org/1999/xlink">

	<!-- main template -->
	<xsl:template match="/">
		<office:document-content xmlns:office="urn:oasis:names:tc:opendocument:xmlns:office:1.0" xmlns:style="urn:oasis:names:tc:opendocument:xmlns:style:1.0" xmlns:text="urn:oasis:names:tc:opendocument:xmlns:text:1.0" xmlns:table="urn:oasis:names:tc:opendocument:xmlns:table:1.0" xmlns:draw="urn:oasis:names:tc:opendocument:xmlns:drawing:1.0" xmlns:fo="urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0" xmlns:xlink="http://www.w3.org/1999/xlink" xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:meta="urn:oasis:names:tc:opendocument:xmlns:meta:1.0" xmlns:number="urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0" xmlns:svg="urn:oasis:names:tc:opendocument:xmlns:svg-compatible:1.0" xmlns:chart="urn:oasis:names:tc:opendocument:xmlns:chart:1.0" xmlns:dr3d="urn:oasis:names:tc:opendocument:xmlns:dr3d:1.0" xmlns:math="http://www.w3.org/1998/Math/MathML" xmlns:form="urn:oasis:names:tc:opendocument:xmlns:form:1.0" xmlns:script="urn:oasis:names:tc:opendocument:xmlns:script:1.0" xmlns:ooo="http://openoffice.org/2004/office" xmlns:ooow="http://openoffice.org/2004/writer" xmlns:oooc="http://openoffice.org/2004/calc" xmlns:dom="http://www.w3.org/2001/xml-events" xmlns:xforms="http://www.w3.org/2002/xforms" xmlns:xsd="http://www.w3.org/2001/XMLSchema" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" office:version="1.0">
			<office:automatic-styles>
				<style:style style:name="gbg" style:family="table-cell" style:parent-style-name="Default">
					<style:table-cell-properties fo:background-color="#00A000"/>
				</style:style>
				<style:style style:name="rbg" style:family="table-cell" style:parent-style-name="Default">
					<style:table-cell-properties fo:background-color="#854040"/>
				</style:style>
				<style:style style:name="nbg" style:family="table-cell" style:parent-style-name="Default">
					<style:table-cell-properties fo:background-color="#FFFFFF"/>
				</style:style>
			</office:automatic-styles>
			<office:body>
				<xsl:apply-templates select="results" mode="summary"/>
				<xsl:apply-templates select="results/benchmarks" mode="single-details"/>
			</office:body>
		</office:document-content>
	</xsl:template>
	<xsl:key name="bsbbf_sum" match="file" use="@name"/>

	<xsl:template name="summaryAggregates">
		<xsl:param name="curStatus" />
		<xsl:param name="nrOfBenchmarks" />
		<xsl:variable name="beforeArea">INDIRECT(ADDRESS(1; CELL("COL")-1) &amp; ":" &amp; ADDRESS(<xsl:value-of select="$nrOfBenchmarks+1"/>; CELL("COL")-1))</xsl:variable>
		<xsl:variable name="curArea">INDIRECT(ADDRESS(1; CELL("COL")) &amp; ":" &amp; ADDRESS(<xsl:value-of select="$nrOfBenchmarks+1"/>; CELL("COL")))</xsl:variable>
		<xsl:variable name="afterArea">INDIRECT(ADDRESS(1; CELL("COL")+1) &amp; ":" &amp; ADDRESS(<xsl:value-of select="$nrOfBenchmarks+1"/>; CELL("COL")+1))</xsl:variable>
		<table:table-row>
			<table:table-cell>
				<xsl:attribute name="office:value"><xsl:value-of select="$curStatus"/></xsl:attribute>
				<text:p><xsl:value-of select="$curStatus"/></text:p>
			</table:table-cell>
			<xsl:for-each select="/results/solvers/solver">
				<table:table-cell><xsl:attribute name="table:formula">=SUMIF(<xsl:value-of select="$afterArea"/>; "<xsl:value-of select="$curStatus"/>"; <xsl:value-of select="$curArea"/>)</xsl:attribute></table:table-cell>
				<table:table-cell><xsl:attribute name="table:formula">=COUNTIF(<xsl:value-of select="$curArea"/>; "<xsl:value-of select="$curStatus"/>")</xsl:attribute></table:table-cell>
			</xsl:for-each>
		</table:table-row>
	</xsl:template>
	
	<xsl:template name="allSummaryAggregates">
		<xsl:param name="nrOfBenchmarks" />
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'sat'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'unsat'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'unknown'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'wrong'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'error'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'timeout'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'memout'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'no answer'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'segmentation fault'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'segfault'" />
		</xsl:call-template>
		<xsl:call-template name="summaryAggregates">
			<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
			<xsl:with-param name="curStatus" select="'abort'" />
		</xsl:call-template>
	</xsl:template>
	
	<xsl:template name="singleResultRow">
		<xsl:param name="FILE" />
		<xsl:for-each select="/results/solvers/solver">
			<xsl:variable name="id"><xsl:value-of select='@solver_id'/></xsl:variable>
			<table:table-cell office:value-type="float">
				<xsl:attribute name="office:value">
					<xsl:value-of select="$FILE/run[@solver_id=$id]/results/result[@name='runtime']"/>
				</xsl:attribute>
				<text:p>
					<xsl:value-of select="translate($FILE/run[@solver_id=$id]/results/result[@name='runtime'], '\smsec', ' ')"/>
				</text:p>
			</table:table-cell>
			<table:table-cell>
				<xsl:attribute name="office:value">
					<xsl:value-of select="$FILE/run[@solver_id=$id]/results/result[@name='answer']"/>
				</xsl:attribute>
				<xsl:attribute name="table:style-name">
					<xsl:choose>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'sat'">nbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'unsat'">nbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'unknown'">nbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'error'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'wrong'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'timeout'">nbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'memout'">nbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'no answer'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'segmentation fault'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'segfault'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='answer'] = 'abort'">rbg</xsl:when>
						<xsl:when test="$FILE/run[@solver_id=$id]/results/result[@name='validated'] = 'true'">gbg</xsl:when>
						<xsl:otherwise>nbg</xsl:otherwise>
					</xsl:choose>
				</xsl:attribute>
				<text:p>
					<xsl:value-of select="$FILE/run[@solver_id=$id]/results/result[@name='answer']"/>
				</text:p>
			</table:table-cell>
		</xsl:for-each>
	</xsl:template>

	<!-- summary sheet -->
	<xsl:template match="results" mode="summary">
		<xsl:variable name="nrOfBenchmarks" select="count(benchmarks/file)"/>
		<office:spreadsheet>
			<table:table>
				<xsl:attribute name="table:name">all</xsl:attribute>
				
				<!-- header -->
				<table:table-row>
					<table:table-cell/>
					<xsl:for-each select="//solvers/solver">
						<table:table-cell>
							<xsl:attribute name="office:value">
								<xsl:value-of select='@solver_id'/>
							</xsl:attribute>
							<text:p>
								<xsl:value-of select="@solver_id"/>
							</text:p>
						</table:table-cell>
						<table:table-cell/>
					</xsl:for-each>
				</table:table-row>
				<xsl:for-each select="benchmarks/file">
					<table:table-row>
						<table:table-cell>
							<xsl:attribute name="office:value">
								<xsl:value-of select="@name"/>
							</xsl:attribute>
							<text:p>
								<xsl:value-of select="@name"/>
							</text:p>
						</table:table-cell>
						<xsl:call-template name="singleResultRow">
							<xsl:with-param name="FILE" select="." />
						</xsl:call-template>
					</table:table-row>	
				</xsl:for-each>
				
				<table:table-row>
					<table:table-cell>
						<xsl:attribute name="office:value">count</xsl:attribute>
						<text:p>count</text:p>
					</table:table-cell>
					<xsl:for-each select="/results/solvers/solver">
						<table:table-cell />
						<table:table-cell><xsl:attribute name="table:formula">=COUNT(INDIRECT(ADDRESS(1; CELL("COL")-1) &amp; ":" &amp; ADDRESS(<xsl:value-of select="$nrOfBenchmarks+1"/>; CELL("COL")-1)))</xsl:attribute></table:table-cell>
					</xsl:for-each>
				</table:table-row>
				
				<xsl:call-template name="allSummaryAggregates">
					<xsl:with-param name="nrOfBenchmarks" select="$nrOfBenchmarks" />
				</xsl:call-template>
			</table:table>
		</office:spreadsheet>
	</xsl:template>
	
	<!-- detail sheet for every solver -->
	<xsl:template match="benchmarks" mode="single-details">
		<xsl:variable name="SET" select="."/>
		<xsl:for-each select="/results/solvers/solver">
			<xsl:variable name="SolverID" select="@solver_id"/>
			<office:spreadsheet>
				<table:table>
					<xsl:attribute name="table:name">
						<xsl:value-of select='@solver_id'/>
					</xsl:attribute>
					<table:table-row>
						<table:table-cell/>
						<table:table-cell>
								<xsl:attribute name="office:value">runtime</xsl:attribute>
								<text:p>runtime</text:p>
						</table:table-cell>
						<table:table-cell>
								<xsl:attribute name="office:value">answer</xsl:attribute>
								<text:p>answer</text:p>
						</table:table-cell>
						<xsl:for-each select="/results/statistics/stat">
							<table:table-cell>
								<xsl:attribute name="office:value">
									<xsl:value-of select="@name"/>
								</xsl:attribute>
								<text:p>
									<xsl:value-of select="@name"/>
								</text:p>
							</table:table-cell>
						</xsl:for-each>
					</table:table-row>
					<xsl:for-each select="$SET/file">
						<xsl:variable name="FILE" select="."/>
						<table:table-row>
							<table:table-cell>
								<xsl:attribute name="office:value">
									<xsl:value-of select="@name"/>
								</xsl:attribute>
								<text:p>
									<xsl:value-of select="@name"/>
								</text:p>
							</table:table-cell>
							<table:table-cell>
								<xsl:attribute name="office:value">
									<xsl:value-of select="run[@solver_id=$SolverID]/results/result[@name='runtime']"/>
								</xsl:attribute>
								<text:p>
									<xsl:value-of select="run[@solver_id=$SolverID]/results/result[@name='runtime']"/>
								</text:p>
							</table:table-cell>
							<table:table-cell>
								<xsl:attribute name="office:value">
									<xsl:value-of select="run[@solver_id=$SolverID]/results/result[@name='answer']"/>
								</xsl:attribute>
								<text:p>
									<xsl:value-of select="run[@solver_id=$SolverID]/results/result[@name='answer']"/>
								</text:p>
							</table:table-cell>
							<xsl:for-each select="/results/statistics/stat">
								<xsl:variable name="StatID" select="@name"/>
								<table:table-cell office:value-type="float">
									<xsl:attribute name="office:value">
										<xsl:value-of select="$FILE/run[@solver_id=$SolverID]/statistics/stat[@name=$StatID]"/>
									</xsl:attribute>
									<text:p>
										<xsl:value-of select="$FILE/run[@solver_id=$SolverID]/statistics/stat[@name=$StatID]"/>
									</text:p>
								</table:table-cell>
							</xsl:for-each>
						</table:table-row>
					</xsl:for-each>
				</table:table>
			</office:spreadsheet>
		</xsl:for-each>
	</xsl:template>
</xsl:stylesheet>
