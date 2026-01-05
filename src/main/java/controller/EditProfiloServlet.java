package controller;

import model.beans.Utente;
import services.EditProfiloService;

import javax.servlet.ServletException;
import javax.servlet.annotation.MultipartConfig;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.Part;
import java.io.IOException;
import java.sql.SQLException;

@MultipartConfig
@WebServlet(name = "EditProfiloServlet", urlPatterns = "/EditProfiloServlet/*")
public class EditProfiloServlet extends HttpServlet {
    private EditProfiloService editProfiloService;

    @Override
    public void init() throws ServletException {
        try {
            this.editProfiloService = new EditProfiloService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize EditProfiloService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            String path = request.getPathInfo() == null ? "/" : request.getPathInfo();
            Utente u = (Utente) request.getSession().getAttribute("user");

            if (path.equals("/editImmagine")) {
                try {
                    Part part = request.getPart("modifica");
                    u = editProfiloService.editImmagine(u, part, path);
                    request.getSession().setAttribute("user", u);
                    response.sendRedirect(request.getServletContext().getContextPath() + "/paginaUtente.jsp");

                } catch (SQLException throwables) {
                    throwables.printStackTrace();
                    response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
                }
            } else {
                try {
                    String modifica = request.getParameter("modifica"); // modifica sul db
                    u = editProfiloService.editProfilo(u, modifica, path);
                    request.getSession().setAttribute("user", u);
                    response.sendRedirect(request.getServletContext().getContextPath() + "/paginaUtente.jsp");
                } catch (SQLException throwables) {
                    throwables.printStackTrace();
                    response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
            // Ensure we don't try to send error if response is already committed, but basic
            // safety here
            if (!response.isCommitted()) {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An internal error occurred");
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            doGet(req, resp);
        } catch (Exception e) {
            e.printStackTrace();
            if (!resp.isCommitted()) {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An internal error occurred");
            }
        }
    }
}