package controller;

import javax.servlet.*;
import javax.servlet.annotation.WebFilter;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpServletResponseWrapper;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.zip.GZIPOutputStream;

@WebFilter(filterName = "CompressionFilter", urlPatterns = "/*")
public class CompressionFilter implements Filter {

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {

        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;

        String acceptEncoding = httpRequest.getHeader("Accept-Encoding");
        if (acceptEncoding != null && acceptEncoding.contains("gzip") && isCompressible(httpRequest)) {
            GzipResponseWrapper wrappedResponse = new GzipResponseWrapper(httpResponse);
            try {
                chain.doFilter(request, wrappedResponse);
            } finally {
                wrappedResponse.finishResponse();
            }
        } else {
            chain.doFilter(request, response);
        }
    }

    @Override
    public void destroy() {
    }

    private boolean isCompressible(HttpServletRequest request) {
        String uri = request.getRequestURI();
        String contextPath = request.getContextPath();
        String path = uri.substring(contextPath.length()).toLowerCase();

        // Skip FileServlet images path
        if (path.startsWith("/img/")) {
            return false;
        }

        // Typically compress text-based and extensionless paths (servlets)
        return path.endsWith("landingpage") ||
               path.endsWith(".jsp") ||
               path.endsWith(".css") ||
               path.endsWith(".js") ||
               path.endsWith(".html") ||
               path.endsWith(".ico") ||
               path.endsWith(".json") ||
               path.endsWith(".svg") ||
               !path.contains(".");
    }

    private static class GzipResponseWrapper extends HttpServletResponseWrapper {
        private GzipServletOutputStream gzipOutputStream = null;
        private PrintWriter printWriter = null;

        public GzipResponseWrapper(HttpServletResponse response) {
            super(response);
        }

        @Override
        public ServletOutputStream getOutputStream() throws IOException {
            if (printWriter != null) {
                throw new IllegalStateException("getWriter() has already been called for this response");
            }
            if (gzipOutputStream == null) {
                HttpServletResponse response = (HttpServletResponse) getResponse();
                response.setHeader("Content-Encoding", "gzip");
                gzipOutputStream = new GzipServletOutputStream(response.getOutputStream());
            }
            return gzipOutputStream;
        }

        @Override
        public PrintWriter getWriter() throws IOException {
            if (gzipOutputStream != null) {
                throw new IllegalStateException("getOutputStream() has already been called for this response");
            }
            if (printWriter == null) {
                HttpServletResponse response = (HttpServletResponse) getResponse();
                response.setHeader("Content-Encoding", "gzip");
                gzipOutputStream = new GzipServletOutputStream(response.getOutputStream());
                printWriter = new PrintWriter(new OutputStreamWriter(gzipOutputStream, getResponse().getCharacterEncoding()));
            }
            return printWriter;
        }

        @Override
        public void flushBuffer() throws IOException {
            if (printWriter != null) {
                printWriter.flush();
            } else if (gzipOutputStream != null) {
                gzipOutputStream.flush();
            }
            super.flushBuffer();
        }

        public void finishResponse() throws IOException {
            if (printWriter != null) {
                printWriter.close();
            } else if (gzipOutputStream != null) {
                gzipOutputStream.close();
            }
        }

        @Override
        public void setContentLength(int len) {
            // Ignore downstream attempts to set content length of uncompressed resource
        }

        @Override
        public void setContentLengthLong(long len) {
            // Ignore downstream attempts to set content length of uncompressed resource
        }

        @Override
        public void setHeader(String name, String value) {
            if ("content-length".equalsIgnoreCase(name)) {
                return;
            }
            super.setHeader(name, value);
        }

        @Override
        public void addHeader(String name, String value) {
            if ("content-length".equalsIgnoreCase(name)) {
                return;
            }
            super.addHeader(name, value);
        }

        @Override
        public void setIntHeader(String name, int value) {
            if ("content-length".equalsIgnoreCase(name)) {
                return;
            }
            super.setIntHeader(name, value);
        }
    }

    private static class GzipServletOutputStream extends ServletOutputStream {
        private final ServletOutputStream outputStream;
        private final GZIPOutputStream gzipOutputStream;
        private boolean closed = false;

        public GzipServletOutputStream(ServletOutputStream outputStream) throws IOException {
            this.outputStream = outputStream;
            this.gzipOutputStream = new GZIPOutputStream(outputStream);
        }

        @Override
        public void write(int b) throws IOException {
            if (closed) {
                throw new IOException("Cannot write to a closed output stream");
            }
            gzipOutputStream.write(b);
        }

        @Override
        public void write(byte[] b) throws IOException {
            write(b, 0, b.length);
        }

        @Override
        public void write(byte[] b, int off, int len) throws IOException {
            if (closed) {
                throw new IOException("Cannot write to a closed output stream");
            }
            gzipOutputStream.write(b, off, len);
        }

        @Override
        public void flush() throws IOException {
            if (closed) {
                throw new IOException("Cannot flush a closed output stream");
            }
            gzipOutputStream.flush();
        }

        @Override
        public void close() throws IOException {
            if (closed) {
                return;
            }
            gzipOutputStream.finish();
            gzipOutputStream.close();
            closed = true;
        }

        @Override
        public boolean isReady() {
            return outputStream.isReady();
        }

        @Override
        public void setWriteListener(WriteListener writeListener) {
            outputStream.setWriteListener(writeListener);
        }
    }
}
